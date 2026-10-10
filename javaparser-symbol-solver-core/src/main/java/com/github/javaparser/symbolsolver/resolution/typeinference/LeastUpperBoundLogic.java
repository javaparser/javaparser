/*
 * Copyright (C) 2013-2026 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.symbolsolver.resolution.typeinference;

import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration.Bound;
import com.github.javaparser.resolution.model.typesystem.LazyType;
import com.github.javaparser.resolution.model.typesystem.NullType;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedArrayType;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.ResolvedTypeVariable;
import com.github.javaparser.resolution.types.ResolvedWildcard;
import com.github.javaparser.resolution.types.ResolvedWildcard.BoundType;
import com.github.javaparser.resolution.types.parametrization.ResolvedTypeParametersMap.Builder;
import com.github.javaparser.utils.Pair;
import com.google.common.collect.Lists;
import com.google.common.collect.Multimap;
import com.google.common.collect.Multimaps;
import com.google.common.collect.Sets;
import java.io.Serializable;
import java.util.*;
import java.util.stream.Collectors;

public class LeastUpperBoundLogic {

    // Sets of types whose candidate parameterization is being computed further up the call stack
    private final Set<Set<ResolvedType>> lubsInProgress = new HashSet<>();

    private final TypeSolver typeSolver;

    /**
     * Without a type solver, java.lang.Object cannot be added to the supertypes of interfaces, so the lub of an
     * interface and a type that does not implement it is {@code null}, and neither can Object, Cloneable and
     * Serializable be added to the supertypes of arrays, so the lub of an array and a type that is not an array of
     * reference types is {@code null}. Prefer {@link #of(TypeSolver)}.
     */
    public static LeastUpperBoundLogic of() {
        return new LeastUpperBoundLogic(null);
    }

    /**
     * @param typeSolver used to solve java.lang.Object, a supertype of every interface (JLS 4.10.2)
     */
    public static LeastUpperBoundLogic of(TypeSolver typeSolver) {
        return new LeastUpperBoundLogic(typeSolver);
    }

    private LeastUpperBoundLogic(TypeSolver typeSolver) {
        this.typeSolver = typeSolver;
    }

    /**
     * See JLS 4.10.4. Least Upper Bound.
     * <p>
     * This implementation approximates the lub specified by the JLS: when the minimal erased candidate set contains
     * several types, the lub should be their intersection {@code Best(W1) & ... & Best(Wr)}, but only one of them is
     * returned, classes first, then interfaces in the order of their qualified names.
     *
     * @return the least upper bound of the types, or {@code null} if no shared supertype is found (for example for
     *     primitive types, which have no supertype here)
     */
    public ResolvedType lub(Set<ResolvedType> types) {
        if (types.isEmpty()) {
            throw new IllegalArgumentException();
        }

        // If there is only one type then the lub is the type itself
        if (types.size() == 1) {
            return concreteType(types.iterator().next());
        }

        // The direct supertypes of the null type are all reference types other than the null type itself.
        // One way to handle this case is to remove the type null from the list of types.
        // Provides the concret type of Lazy type if needed
        Set<ResolvedType> resolvedTypes = types.stream()
                .filter(type -> !(type instanceof NullType))
                .map(type -> concreteType(type))
                .collect(Collectors.toSet());

        // reduces the set in the presence of enumeration type because members are
        // not equal and they do not have an explicit super type.
        // So we only keep one enumeration for all the members of an enumeration
        filterEnumType(resolvedTypes);

        // The least upper bound, or "lub", of a set of reference types is a shared supertype that is more specific
        // than any other shared supertype (that is, no other shared supertype is a subtype of the least upper bound).
        // This type, lub(U1, ..., Uk), is determined as follows.
        //
        // If k = 1, then the lub is the type itself: lub(U) = U.

        if (resolvedTypes.size() == 1) {
            return resolvedTypes.stream().findFirst().get();
        }

        // The direct supertypes of an array type S[], S being a reference type, are the arrays T[] of the direct
        // supertypes T of S, then Object, Cloneable and Serializable (JLS 4.10.3). When all the types are arrays of
        // reference types, the minimal erased candidates are therefore the arrays of the minimal erased candidates of
        // the component types. The lub is computed on the component types, as javac does, which also recovers their
        // type arguments: strictly, Best(X[]) is X[] erased, an array type not being a generic type.
        if (resolvedTypes.stream().allMatch(this::isArrayOfReferenceType)) {
            Set<ResolvedType> componentTypes = resolvedTypes.stream()
                    .map(type -> type.asArrayType().getComponentType())
                    .collect(Collectors.toSet());
            ResolvedType componentLub = lub(componentTypes);
            return componentLub == null ? null : new ResolvedArrayType(componentLub);
        }

        // can we have primitive types?

        //
        // Otherwise:
        //
        // For each Ui (1 ≤ i ≤ k):
        //
        // Let ST(Ui) be the set of supertypes of Ui.

        List<Set<ResolvedType>> supertypes = supertypes(resolvedTypes);

        //
        // Let EST(Ui), the set of erased supertypes of Ui, be:
        //
        // EST(Ui) = { |W| | W in ST(Ui) } where |W| is the erasure of W.
        //
        // The reason for computing the set of erased supertypes is to deal with situations where the set of types
        // includes several distinct parameterizations of a generic type.
        //
        // For example, given List<String> and List<Object>, simply intersecting the sets ST(List<String>) = {
        // List<String>, Collection<String>, Object } and ST(List<Object>) = { List<Object>, Collection<Object>, Object
        // } would yield a set { Object }, and we would have lost track of the fact that the upper bound can safely be
        // assumed to be a List.
        //
        // In contrast, intersecting EST(List<String>) = { List, Collection, Object } and EST(List<Object>) = { List,
        // Collection, Object } yields { List, Collection, Object }, which will eventually enable us to produce
        // List<?>.
        //

        List<Set<ResolvedType>> erasedSupertypes = erased(supertypes);

        // Let EC, the erased candidate set for U1 ... Uk, be the intersection of all the sets EST(Ui) (1 ≤ i ≤ k).
        //

        List<ResolvedType> erasedCandidates = intersection(erasedSupertypes);

        // Let MEC, the minimal erased candidate set for U1 ... Uk, be:
        //
        // MEC = { V | V in EC, and for all W ≠ V in EC, it is not the case that W <: V }
        //
        // Because we are seeking to infer more precise types, we wish to filter out any candidates that are supertypes
        // of other candidates.
        // This is what computing MEC accomplishes.
        // In our running example, we had EC = { List, Collection, Object }, so MEC = { List }.

        List<ResolvedType> minimalErasedCandidates = minimalCandidates(erasedCandidates);
        if (minimalErasedCandidates.isEmpty()) {
            return null;
        }

        // The next step is to recover type arguments for the erased types in MEC.
        //
        // For any element G of MEC that is a generic type:
        //
        // Let the "relevant" parameterizations of G, Relevant(G), be:
        //
        // Relevant(G) = { V | 1 ≤ i ≤ k: V in ST(Ui) and V = G<...> }
        //
        // In our running example, the only generic element of MEC is List, and Relevant(List) = { List<String>,
        // List<Object> }.

        Multimap<ResolvedType, ResolvedType> relevantParameterizations =
                relevantParameterizations(minimalErasedCandidates, supertypes);

        // We will now seek to find a type argument for List that contains (§4.5.1) both String and Object.
        //
        // This is done by means of the least containing parameterization (lcp) operation defined below.
        // The first line defines lcp() on a set, such as Relevant(List), as an operation on a list of the elements of
        // the set.
        // The next line defines the operation on such lists, as a pairwise reduction on the elements of the list.
        // The third line is the definition of lcp() on pairs of parameterized types,
        // which in turn relies on the notion of least containing type argument (lcta).
        // lcta() is defined for all possible cases.
        //
        // Let the "candidate" parameterization of G, Candidate(G), be the most specific parameterization of the
        // generic type G that contains all the relevant parameterizations of G:
        //
        // Candidate(G) = lcp(Relevant(G))
        //
        // where lcp(), the least containing invocation, is:
        //
        // lcp(S) = lcp(e1, ..., en) where ei (1 ≤ i ≤ n) in S
        //
        // lcp(e1, ..., en) = lcp(lcp(e1, e2), e3, ..., en)
        //
        // lcp(G<X1, ..., Xn>, G<Y1, ..., Yn>) = G<lcta(X1, Y1), ..., lcta(Xn, Yn)>
        //
        // lcp(G<X1, ..., Xn>) = G<lcta(X1), ..., lcta(Xn)>
        //
        // and where lcta(), the least containing type argument, is: (assuming U and V are types)
        //
        // lcta(U, V) = U if U = V, otherwise ? extends lub(U, V)
        //
        // lcta(U, ? extends V) = ? extends lub(U, V)
        //
        // lcta(U, ? super V) = ? super glb(U, V)
        //
        // lcta(? extends U, ? extends V) = ? extends lub(U, V)
        //
        // lcta(? extends U, ? super V) = ?
        //
        // lcta(? super U, ? super V) = ? super glb(U, V)
        //
        // lcta(U) = ? if U's upper bound is Object, otherwise ? extends lub(U,Object)
        //
        // and where glb() is as defined in §5.1.10.
        //
        // Let lub(U1 ... Uk) be:
        //
        // Best(W1) & ... & Best(Wr)
        //
        // where Wi (1 ≤ i ≤ r) are the elements of MEC, the minimal erased candidate set of U1 ... Uk;
        //
        // and where, if any of these elements are generic, we use the candidate parameterization (so as to recover
        // type arguments):
        //
        // Best(X) = Candidate(X) if X is generic; X otherwise.
        //
        // Strictly speaking, this lub() function only approximates a least upper bound.
        // Formally, there may exist some other type T such that all of U1 ... Uk are subtypes of T and T is a subtype
        // of lub(U1, ..., Uk).
        // However, a compiler for the Java programming language must implement lub() as specified above.
        //

        ResolvedType erasedBest = best(minimalErasedCandidates);

        // It is possible that the lub() function yields an infinite type.
        // This is permissible, and a compiler for the Java programming language must recognize such situations and
        // represent them appropriately using cyclic data structures.
        //
        // The possibility of an infinite type stems from the recursive calls to lub().
        // Readers familiar with recursive types should note that an infinite type is not the same as a recursive type.
        Collection<ResolvedType> erasedTypeParameterizations = relevantParameterizations.get(erasedBest);
        if (!erasedTypeParameterizations.contains(erasedBest)) {
            Set<ResolvedType> searchedTypes = new HashSet<>(resolvedTypes);
            // if the lub of these types is already being computed further up the call stack (infinite type),
            // we interrupt calculation and use the erasure of the parameterized type instead
            if (lubsInProgress.add(searchedTypes)) {
                try {
                    return leastContainingParameterization(new ArrayList<>(erasedTypeParameterizations));
                } finally {
                    lubsInProgress.remove(searchedTypes);
                }
            }
        }
        return erasedBest;
    }

    /*
     * Provides concrete type of Lazy type
     */
    private ResolvedType concreteType(ResolvedType type) {
        return type instanceof LazyType ? LazyType.class.cast(type).getType() : type;
    }

    /*
     * Check the type declaration if it is an enum
     */
    private boolean isEnum(ResolvedType type) {
        return type.isReferenceType()
                && type.asReferenceType().getTypeDeclaration().get().isEnum();
    }

    /*
     * Keep only one enum reference type per enum declaration
     */
    private void filterEnumType(Set<ResolvedType> resolvedTypes) {
        Map<String, ResolvedType> enumTypes = new HashMap<>();
        List<ResolvedType> erasedEnumTypes = new ArrayList<>();
        for (ResolvedType type : resolvedTypes) {
            if (isEnum(type)) {
                // enum qualified name i.e. java.math.RoundingMode
                String qn = type.asReferenceType()
                        .getTypeDeclaration()
                        .get()
                        .asEnum()
                        .getQualifiedName();
                // Save the first occurrence and mark the others so they can be deleted
                ResolvedType returnedType = enumTypes.putIfAbsent(qn, type);
                if (returnedType != null) {
                    erasedEnumTypes.add(type);
                }
            }
        }
        resolvedTypes.removeAll(erasedEnumTypes);
    }

    private List<Set<ResolvedType>> supertypes(Set<ResolvedType> types) {
        return types.stream()
                .map(type -> supertypes(type).stream().collect(Collectors.toCollection(LinkedHashSet::new)))
                .collect(Collectors.toList());
    }

    private Set<ResolvedType> supertypes(ResolvedType type) {
        ResolvedType concreteType = concreteType(type);
        if (concreteType.isTypeVariable()) return supertypes(concreteType.asTypeVariable());
        if (concreteType.isArray()) return supertypes(concreteType.asArrayType());
        return concreteType.isReferenceType() ? supertypes(concreteType.asReferenceType()) : new LinkedHashSet<>();
    }

    private boolean isArrayOfReferenceType(ResolvedType type) {
        return type.isArray()
                && !concreteType(type.asArrayType().getComponentType()).isPrimitive();
    }

    /*
     * Object, Cloneable and Serializable are supertypes of every array type (JLS 4.10.3). The arrays of the
     * supertypes of the component type are left out: they can only be shared supertypes when all the types are
     * arrays of reference types, a case that lub computes on the component types.
     */
    private Set<ResolvedType> supertypes(ResolvedArrayType arrayType) {
        Set<ResolvedType> supertypes = new LinkedHashSet<>();
        supertypes.add(arrayType);
        if (typeSolver != null) {
            supertypes.add(new ReferenceTypeImpl(typeSolver.getSolvedJavaLangObject()));
            supertypes.add(new ReferenceTypeImpl(typeSolver.solveType(Cloneable.class.getCanonicalName())));
            supertypes.add(new ReferenceTypeImpl(typeSolver.solveType(Serializable.class.getCanonicalName())));
        }
        return supertypes;
    }

    /*
     * The direct supertypes of a type variable are the types listed in its bound (JLS 4.10.2), with their type
     * arguments, so the supertypes of all its bounds are kept. The type variable itself is left out: it is not a
     * parameterization of a generic type, and its erasure, the erasure of its leftmost bound, is already among the
     * erased supertypes of the bound.
     */
    private Set<ResolvedType> supertypes(ResolvedTypeVariable typeVariable) {
        List<ResolvedType> upperBounds = typeVariable.asTypeParameter().getBounds().stream()
                .filter(Bound::isExtends)
                .map(Bound::getType)
                .collect(Collectors.toList());
        if (upperBounds.isEmpty()) {
            return supertypes(typeVariable.erasure());
        }
        Set<ResolvedType> supertypes = new LinkedHashSet<>();
        upperBounds.forEach(bound -> supertypes.addAll(supertypes(bound)));
        return supertypes;
    }

    private Set<ResolvedType> supertypes(ResolvedReferenceType type) {
        Set<ResolvedType> supertypes = new LinkedHashSet<>();
        supertypes.add(type);
        // The supertypes of a raw type are the erasures of its supertypes (JLS 4.8). A raw supertype written in the
        // source code (class ChildRaw extends Child) is represented as the generic type parameterized by its own
        // type variables (Child<Y>), so the ancestors that mention type variables out of the scope of the type are
        // inherited through a raw type and are erased as well.
        Set<String> typeVariableContainers = typeVariableContainers(type);
        for (ResolvedReferenceType ancestor : type.getAllAncestors()) {
            supertypes.add(
                    type.isRawType() || mentionsTypeVariableOutOfScope(ancestor, typeVariableContainers)
                            ? ancestor.erasure()
                            : ancestor);
        }
        // Object is a supertype of every interface (JLS 4.10.2), but getAllAncestors() does not return it for
        // interfaces: without it, the erased candidate set of an interface and a class not implementing it is empty
        if (typeSolver != null && supertypes.stream().noneMatch(this::isJavaLangObject)) {
            supertypes.add(new ReferenceTypeImpl(typeSolver.getSolvedJavaLangObject()));
        }
        return supertypes;
    }

    /*
     * Ids of the type declarations whose type variables are in the scope of the type: its own declaration and the
     * declarations enclosing it.
     */
    private Set<String> typeVariableContainers(ResolvedReferenceType type) {
        Set<String> containers = new HashSet<>();
        Optional<ResolvedReferenceTypeDeclaration> declaration = type.getTypeDeclaration();
        while (declaration.isPresent()) {
            containers.add(declaration.get().getId());
            declaration = declaration.get().containerType();
        }
        return containers;
    }

    /*
     * Type variables declared on methods are left aside: they are the type arguments of generic method calls that
     * were not inferred.
     */
    private boolean mentionsTypeVariableOutOfScope(ResolvedType type, Set<String> typeVariableContainers) {
        ResolvedType concreteType = concreteType(type);
        if (concreteType.isTypeVariable()) {
            ResolvedTypeParameterDeclaration typeParameter =
                    concreteType.asTypeVariable().asTypeParameter();
            return typeParameter.declaredOnType() && !typeVariableContainers.contains(typeParameter.getContainerId());
        }
        if (concreteType.isWildcard()) {
            return concreteType.asWildcard().isBounded()
                    && mentionsTypeVariableOutOfScope(
                            concreteType.asWildcard().getBoundedType(), typeVariableContainers);
        }
        if (concreteType.isArray()) {
            return mentionsTypeVariableOutOfScope(
                    concreteType.asArrayType().getComponentType(), typeVariableContainers);
        }
        if (concreteType.isReferenceType()) {
            return concreteType.asReferenceType().typeParametersValues().stream()
                    .anyMatch(typeArgument -> mentionsTypeVariableOutOfScope(typeArgument, typeVariableContainers));
        }
        return false;
    }

    private boolean isJavaLangObject(ResolvedType type) {
        return type.isReferenceType() && type.asReferenceType().isJavaLangObject();
    }

    private List<Set<ResolvedType>> erased(List<Set<ResolvedType>> typeSets) {
        return typeSets.stream()
                .map(set ->
                        set.stream().map(ResolvedType::erasure).collect(Collectors.toCollection(LinkedHashSet::new)))
                .collect(Collectors.toList());
    }

    private List<ResolvedType> intersection(List<Set<ResolvedType>> supertypes) {
        return new ArrayList<>(supertypes.stream().reduce(union(supertypes), Sets::intersection));
    }

    private Set<ResolvedType> union(List<Set<ResolvedType>> supertypes) {
        return supertypes.stream().flatMap(Collection::stream).collect(Collectors.toCollection(LinkedHashSet::new));
    }

    /**
     * Let MEC, the minimal erased candidate set for U1 ... Uk, be:
     * MEC = { V | V in EC, and for all W != V in EC, it is not the case that W <: V }
     *
     * @param erasedCandidates
     * @return
     */
    private List<ResolvedType> minimalCandidates(List<ResolvedType> erasedCandidates) {
        List<ResolvedType> results = new ArrayList<>();
        for (ResolvedType v : erasedCandidates) {
            if (erasedCandidates.stream().noneMatch(w -> !w.equals(v) && v.isAssignableBy(w))) {
                results.add(v);
            }
        }
        return results;
    }

    /**
     * For any element G of MEC that is a generic type, let the "relevant" parameterizations of G, Relevant(G), be:
     * Relevant(G) = { V | 1 ≤ i ≤ k: V in ST(Ui) and V = G<...> }
     *
     * @param minimalErasedCandidates MEC
     * @param supertypes
     * @return the set of known parameterizations for each generic type G of MEC
     */
    private Multimap<ResolvedType, ResolvedType> relevantParameterizations(
            List<ResolvedType> minimalErasedCandidates, List<Set<ResolvedType>> supertypes) {
        Multimap<ResolvedType, ResolvedType> result = Multimaps.newSetMultimap(new HashMap<>(), LinkedHashSet::new);
        for (Set<ResolvedType> supertypesSet : supertypes) {
            for (ResolvedType supertype : supertypesSet) {
                ResolvedType erasedSupertype = supertype.erasure();
                if (minimalErasedCandidates.contains(erasedSupertype)) {
                    result.put(erasedSupertype, supertype);
                }
            }
        }
        return result;
    }

    private ResolvedType best(List<ResolvedType> minimalCandidates) {
        Collections.sort(minimalCandidates, (t1, t2) -> {
            // Sort minimal candidates by name with classes before interfaces, to guarantee always the same type is
            // returned when approximated.
            ResolvedReferenceTypeDeclaration t1Symbol =
                    t1.asReferenceType().getTypeDeclaration().get();
            ResolvedReferenceTypeDeclaration t2Symbol =
                    t2.asReferenceType().getTypeDeclaration().get();
            if (t1Symbol.isInterface() && t2Symbol.isInterface()) {
                return t1Symbol.getQualifiedName().compareTo(t2Symbol.getQualifiedName());
            }
            if (t1Symbol.isInterface()) {
                return 1;
            }
            if (t2Symbol.isInterface()) {
                return -1;
            }
            return t1Symbol.getQualifiedName().compareTo(t2Symbol.getQualifiedName());
        });
        return minimalCandidates.get(0);
    }

    /*
     * Let the "candidate" parameterization of G, Candidate(G), be the most specific parameterization of the generic
     * type G that contains all * the relevant parameterizations of G:
     * Candidate(G) = lcp(Relevant(G)),
     * where lcp(), the least containing invocation, is:
     * lcp(S) = lcp(e1, ..., en) where ei (1 ≤ i ≤ n) in S
     * lcp(e1, ..., en) = lcp(lcp(e1, e2), e3, ..., en)
     */
    private ResolvedType leastContainingParameterization(List<ResolvedType> types) {
        if (types.size() == 1) {
            return types.get(0);
        }
        ResolvedType type1 = types.get(0);
        ResolvedType type2 = types.get(1);
        ResolvedType reduction = leastContainingParameterization(type1, type2);

        List<ResolvedType> reducedList = Lists.newArrayList(reduction);
        reducedList.addAll(types.subList(2, types.size()));

        return leastContainingParameterization(reducedList);
    }

    /*
     * lcp(G<X1, ..., Xn>, G<Y1, ..., Yn>) = G<lcta(X1, Y1), ..., lcta(Xn, Yn)>
     * lcp(G<X1, ..., Xn>) = G<lcta(X1), ..., lcta(Xn)>
     */
    private ResolvedType leastContainingParameterization(ResolvedType type1, ResolvedType type2) {

        TypeSubstitution substitution1 = substitution(type1.asReferenceType().getTypeParametersMap());
        TypeSubstitution substitution2 = substitution(type2.asReferenceType().getTypeParametersMap());

        TypeSubstitution typeSubstitution = TypeSubstitution.empty();
        for (ResolvedTypeParameterDeclaration typeDecl : substitution1.typeParameterDeclarations()) {
            // type arguments of ancestors declared in source code are lazy, and LazyType does not define equality
            ResolvedType subs1 = concreteType(substitution1.substitutedType(typeDecl));
            ResolvedType subs2 = concreteType(substitution2.substitutedType(typeDecl));
            subs1 = isSubstituable(subs1) && subs2.isReferenceType() ? subs2 : subs1;
            subs2 = isSubstituable(subs2) && subs1.isReferenceType() ? subs1 : subs2;
            ResolvedType newType = lcta(subs1, subs2);
            typeSubstitution.withPair(typeDecl, newType);
        }

        return substituteType(type1, typeSubstitution);
    }

    /*
     * In case where the {@code ResolvedType} is an unbounded type variable of a method, it is a type argument of a
     * generic method call that was not inferred, and it can be substituted by the other reference type. For example
     * lcp(ArrayList<String>, List<T>) where List<T> is the type of Collections.emptyList() should be List<String>.
     * This is not part of JLS 4.10.4. The type variables of types are real types and are not substituted.
     * The bounds checked are those of the type variable itself, not those of the type parameter of the generic
     * type: in lcp(List<String>, List<T extends Number>), T cannot be substituted by String.
     */
    private boolean isSubstituable(ResolvedType type) {
        if (!type.isTypeVariable()) {
            return false;
        }
        ResolvedTypeParameterDeclaration typeParameter = type.asTypeVariable().asTypeParameter();
        return typeParameter.declaredOnMethod() && (!typeParameter.hasBound() || boundedAsObject(typeParameter));
    }

    private boolean boundedAsObject(ResolvedTypeParameterDeclaration typeDecl) {
        List<Bound> bounds = typeDecl.getBounds();
        return bounds.size() == 1 && bounds.get(0).getType().equals(typeDecl.object());
    }

    private ResolvedType substituteType(ResolvedType type1, TypeSubstitution typeSubstitution) {
        Builder typeParametersMapBuilder = type1.asReferenceType().typeParametersMap().toBuilder();
        for (ResolvedTypeParameterDeclaration rtpd : typeSubstitution.typeParameterDeclarations) {
            typeParametersMapBuilder.setValue(rtpd, typeSubstitution.substitutedType(rtpd));
        }
        return type1.asReferenceType().deriveTypeParameters(typeParametersMapBuilder.build());
    }

    /*
     * This is a data container that maps typeParameterDeclarations with resolvedTypes
     */
    static class TypeSubstitution {

        private List<ResolvedTypeParameterDeclaration> typeParameterDeclarations;
        private List<ResolvedType> types;

        public static TypeSubstitution empty() {
            return new TypeSubstitution();
        }

        private TypeSubstitution() {
            this.typeParameterDeclarations = new LinkedList<>();
            this.types = new LinkedList<>();
        }

        public void withPair(ResolvedTypeParameterDeclaration typeParameterDeclaration, ResolvedType type) {
            this.typeParameterDeclarations.add(typeParameterDeclaration);
            this.types.add(type);
        }

        public List<ResolvedTypeParameterDeclaration> typeParameterDeclarations() {
            return typeParameterDeclarations;
        }

        public ResolvedType substitutedType(ResolvedTypeParameterDeclaration typeDecl) {
            int index = typeParameterDeclarations.indexOf(typeDecl);
            return index > -1 ? types.get(index) : typeDecl.object();
        }
    }

    private TypeSubstitution substitution(List<Pair<ResolvedTypeParameterDeclaration, ResolvedType>> pairs) {
        TypeSubstitution substitution = TypeSubstitution.empty();
        pairs.stream().forEach(pair -> substitution.withPair(pair.a, pair.b));
        return substitution;
    }

    /*
     * the least containing type argument, is: (assuming U and V are types)
     * lcta(U, V) = U if U = V, otherwise ? extends lub(U, V)
     * lcta(U, ? extends V) = ? extends lub(U, V)
     * lcta(U, ? super V) = ? super glb(U, V)
     * lcta(? extends U, ? extends V) = ? extends lub(U, V)
     * lcta(? extends U, ? super V) = ?
     * lcta(? super U, ? super V) = ? super glb(U, V)
     * lcta(U) = ? if U's upper bound is Object, otherwise ? extends lub(U,Object)
     * and where glb() is as defined in §5.1.10.
     */
    private ResolvedType lcta(ResolvedType type1, ResolvedType type2) {
        boolean isWildcard1 = type1.isWildcard();
        boolean isWildcard2 = type2.isWildcard();

        ResolvedType result;
        if (type1.equals(type2)) {
            // lcta(U, V) = U if U = V
            result = type1;
        } else if (isWildcard1 && isWildcard2) {
            result = lctaBothWildcards(type1.asWildcard(), type2.asWildcard());
        } else if (isWildcard1 ^ isWildcard2) {
            ResolvedType rawType = isWildcard1 ? type2 : type1;
            ResolvedWildcard wildcardType = (ResolvedWildcard) (isWildcard1 ? type1 : type2);
            result = lctaOneWildcard(rawType, wildcardType);
        } else {
            // otherwise lcta(U, V) = ? extends lub(U, V)
            result = lctaNoWildcard(type1, type2);
        }
        return result;
    }

    /*
     * lcta(U, V) = U if U = V, otherwise ? extends lub(U, V)
     */
    private ResolvedType lctaNoWildcard(ResolvedType type1, ResolvedType type2) {
        ResolvedType lub = lub(toSet(type1, type2));
        return bound(lub, BoundType.EXTENDS);
    }

    private ResolvedType lctaOneWildcard(ResolvedType rawType, ResolvedWildcard wildcardType) {
        // lcta(U, ?) = lcta(U, ? extends Object) = ? extends lub(U, Object) = ?
        if (!wildcardType.isBounded()) {
            return ResolvedWildcard.UNBOUNDED;
        }
        // lcta(U, ? super V) = ? super glb(U, V)
        if (wildcardType.isSuper()) {
            ResolvedType glb = TypeHelper.glb(toSet(rawType, wildcardType.getBoundedType()));
            return bound(glb, BoundType.SUPER);
        }
        // lcta(U, ? extends V) = ? extends lub(U, V)
        ResolvedType lub = lub(toSet(rawType, wildcardType.getBoundedType()));
        return bound(lub, BoundType.EXTENDS);
    }

    private ResolvedType lctaBothWildcards(ResolvedWildcard type1, ResolvedWildcard type2) {
        // ? is ? extends Object: lcta(? extends U, ?) = ? extends lub(U, Object) = ? and lcta(? super U, ?) = ?
        if (!type1.isBounded() || !type2.isBounded()) {
            return ResolvedWildcard.UNBOUNDED;
        }
        // lcta(? super U, ? super V) = ? super glb(U, V)
        if (type1.isSuper() && type2.isSuper()) {
            ResolvedType glb = TypeHelper.glb(toSet(type1.getBoundedType(), type2.getBoundedType()));
            return bound(glb, BoundType.SUPER);
        }
        // lcta(? extends U, ? extends V) = ? extends lub(U, V)
        if (type1.isExtends() && type2.isExtends()) {
            ResolvedType lub = lub(toSet(type1.getBoundedType(), type2.getBoundedType()));
            return bound(lub, BoundType.EXTENDS);
        }
        // lcta(? extends U, ? super V) = ?
        return ResolvedWildcard.UNBOUNDED;
    }

    // Replace all type parameters in generic types with their bounds or Object if the type parameters are unbounded.

    /*
     * Returns the corresponding wildcard type. {@code ? extends Object} is returned as the unbounded wildcard
     * {@code ?}, and {@code ? super Object} as {@code Object}, the only type it contains.
     */
    private ResolvedType bound(ResolvedType type, BoundType boundType) {
        boolean isObject =
                type != null && type.isReferenceType() && type.asReferenceType().isJavaLangObject();
        if (boundType == BoundType.EXTENDS) {
            return isObject ? ResolvedWildcard.UNBOUNDED : ResolvedWildcard.extendsBound(type);
        }
        return isObject ? type : ResolvedWildcard.superBound(type);
    }

    private Set<ResolvedType> toSet(ResolvedType... resolvedTypes) {
        return new HashSet<>(Arrays.asList(resolvedTypes));
    }
}
