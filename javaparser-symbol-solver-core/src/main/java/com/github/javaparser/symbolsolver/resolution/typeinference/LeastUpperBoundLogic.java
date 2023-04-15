package com.github.javaparser.symbolsolver.resolution.typeinference;

import java.util.*;
import java.util.stream.Collectors;

import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration.Bound;
import com.github.javaparser.resolution.model.typesystem.NullType;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.ResolvedWildcard;
import com.github.javaparser.resolution.types.ResolvedWildcard.BoundType;
import com.github.javaparser.resolution.types.parametrization.ResolvedTypeParametersMap.Builder;
import com.github.javaparser.utils.Pair;
import com.google.common.collect.Lists;
import com.google.common.collect.Multimap;
import com.google.common.collect.Multimaps;
import com.google.common.collect.Sets;

public class LeastUpperBoundLogic {

    private Set<Set<ResolvedType>> lubCache = new HashSet<>();

    public static LeastUpperBoundLogic of() {
    	return new LeastUpperBoundLogic();
    }

    private LeastUpperBoundLogic() {}

    /**
     * See JLS 4.10.4. Least Upper Bound.
     */
    public ResolvedType lub(Set<ResolvedType> types) {
        if (types.isEmpty()) {
            throw new IllegalArgumentException();
        }

        // The direct supertypes of the null type are all reference types other than the null type itself.
        // One way to handle this case is to remove the type null from the list of types.
        Set<ResolvedType> resolvedTypes = types.stream().filter(type -> !(type instanceof NullType)).collect(Collectors.toSet());


        // The least upper bound, or "lub", of a set of reference types is a shared supertype that is more specific
        // than any other shared supertype (that is, no other shared supertype is a subtype of the least upper bound).
        // This type, lub(U1, ..., Uk), is determined as follows.
        //
        // If k = 1, then the lub is the type itself: lub(U) = U.

        if (resolvedTypes.size() == 1) {
            return resolvedTypes.stream().findFirst().get();
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

        Multimap<ResolvedType, ResolvedType> relevantParameterizations = relevantParameterizations(
                minimalErasedCandidates, supertypes);

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
        // lcta(? extends U, ? super V) = U if U = V, otherwise ?
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
        if (erasedTypeParameterizations != null && !erasedTypeParameterizations.contains(erasedBest)) {
            Set<ResolvedType> searchedTypes = new HashSet<>(resolvedTypes);
            // if we already encountered these types in LUB calculation,
            // we interrupt calculation and use the erasure of the parameterized type instead
            if (!lubCache.contains(searchedTypes)) {
                lubCache.add(searchedTypes);
                return leastContainingParameterization(new ArrayList<>(erasedTypeParameterizations));
            }
        }
        return erasedBest;
    }

    private List<Set<ResolvedType>> supertypes(Set<ResolvedType> types) {
        return types.stream()
                .map(type -> supertypes(type).stream().collect(Collectors.toCollection(LinkedHashSet::new)))
                .collect(Collectors.toList());
    }

    private Set<ResolvedType> supertypes(ResolvedType type) {
    	// How to deal with other types like for example type variable?
        return type.isReferenceType() ? supertypes(type.asReferenceType())
                : new LinkedHashSet<>();
    }

    private Set<ResolvedType> supertypes(ResolvedReferenceType type) {
        Set<ResolvedType> supertypes = new LinkedHashSet<>();
        supertypes.add(type);
        supertypes.addAll(type.getAllAncestors());
        return supertypes;
    }

    private List<Set<ResolvedType>> erased(List<Set<ResolvedType>> typeSets) {
        return typeSets.stream()
                .map(set -> set.stream().map(ResolvedType::erasure)
                        .collect(Collectors.toCollection(LinkedHashSet::new)))
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
    private Multimap<ResolvedType, ResolvedType> relevantParameterizations(List<ResolvedType> minimalErasedCandidates,
                                                                           List<Set<ResolvedType>> supertypes) {
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
            ResolvedReferenceTypeDeclaration t1Symbol = t1.asReferenceType().getTypeDeclaration().get();
            ResolvedReferenceTypeDeclaration t2Symbol = t2.asReferenceType().getTypeDeclaration().get();
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
        ResolvedType reduction = leastContainingTypeArgument(type1, type2);

        List<ResolvedType> reducedList = Lists.newArrayList(reduction);
        reducedList.addAll(types.subList(2, types.size()));

        return leastContainingParameterization(reducedList);
    }

    /*
     * lcp(G<X1, ..., Xn>, G<Y1, ..., Yn>) = G<lcta(X1, Y1), ..., lcta(Xn, Yn)>
     * lcp(G<X1, ..., Xn>) = G<lcta(X1), ..., lcta(Xn)>
     */
    private ResolvedType leastContainingTypeArgument(ResolvedType type1, ResolvedType type2) {

        TypeSubstitution substitution1 = substitution(type1.asReferenceType().getTypeParametersMap());
        TypeSubstitution substitution2 = substitution(type2.asReferenceType().getTypeParametersMap());

        TypeSubstitution typeSubstitution = TypeSubstitution.empty();
        for (ResolvedTypeParameterDeclaration typeDecl : substitution1.typeParameterDeclarations()) {
            ResolvedType subs1 = substitution1.substitutedType(typeDecl);
            ResolvedType subs2 = substitution2.substitutedType(typeDecl);
            subs1 = isSubstituable(typeDecl, subs1) && subs2.isReferenceType() ? subs2 : subs1;
            subs2 = isSubstituable(typeDecl, subs2) && subs1.isReferenceType() ? subs1 : subs2;
            ResolvedType newType = lcta(subs1, subs2);
            typeSubstitution.withPair(typeDecl, newType);
        }

        return typeSubstitution.isEmpty() ? lcta(type1, type2) : substituteType(type1, typeSubstitution);
    }

    /*
     * In case where the {@code ResolvedType} is an unbounded type variable,
     * then the type can be can substituted by other reference type. For example
     * the result of lcta(List<String>, List<T>) should be in List<String>.
     */
    private boolean isSubstituable(ResolvedTypeParameterDeclaration typeDecl, ResolvedType type) {
    	return type.isTypeVariable() && (!typeDecl.hasBound() || boundedAsObject(typeDecl));
    }

    private boolean boundedAsObject(ResolvedTypeParameterDeclaration typeDecl) {
    	List<Bound> bounds = typeDecl.getBounds();
    	return bounds.size() == 1 && bounds.get(0).getType().equals(typeDecl.object());
    }

    private ResolvedType substituteType(ResolvedType type1, TypeSubstitution typeSubstitution) {
        Builder  typeParametersMapBuilder = type1.asReferenceType().typeParametersMap().toBuilder();
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

        private final static TypeSubstitution EMPTY = new TypeSubstitution();

        public static TypeSubstitution empty() {
            return new TypeSubstitution();
        }

        private TypeSubstitution() {
            this.typeParameterDeclarations = new LinkedList<>();
            this.types = new LinkedList<>();
        }

        public boolean isEmpty() {
            return this == EMPTY;
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
     * lcta(? extends U, ? super V) = U if U = V, otherwise ?
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
        if (wildcardType.isUpperBounded()) {
            ResolvedType glb = TypeHelper.glb(toSet(rawType, wildcardType.getBoundedType()));
            return bound(glb, BoundType.SUPER);
        }
        ResolvedType lub = lub(toSet(rawType, wildcardType.getBoundedType()));
        return bound(lub, BoundType.EXTENDS);
    }

    private ResolvedType lctaBothWildcards(ResolvedWildcard type1, ResolvedWildcard type2) {
        // lcta(? super U, ? super V) = ? super glb(U, V)
        if (type1.isUpperBounded() && type2.isUpperBounded()) {
            ResolvedType glb = TypeHelper.glb(toSet(type1.getBoundedType(), type2.getBoundedType()));
            return bound(glb, BoundType.SUPER);
        }
        // lcta(? extends U, ? extends V) = ? extends lub(U, V)
        if (type1.isLowerBounded() && type2.isLowerBounded()) {
            ResolvedType lub = lub(toSet(type1.getBoundedType(), type2.getBoundedType()));
            return bound(lub, BoundType.EXTENDS);
        }
        // lcta(? extends U, ? super V) = U if U = V, otherwise ?
        if (type1.getBoundedType().equals(type2.getBoundedType())) {
            return type1.getBoundedType();
        }
        return ResolvedWildcard.UNBOUNDED;
    }

    // Replace all type parameters in generic types with their bounds or Object if the type parameters are unbounded.

    /*
     * Returns the corresponding wildcard type or Object if we want to build a wildcard type like {@code ? extends
     * Object}
     */
    private ResolvedType bound(ResolvedType type, BoundType boundType) {
        if (type != null && type.isReferenceType() && type.asReferenceType().isJavaLangObject()) return type;
        return boundType.equals(BoundType.EXTENDS) ? ResolvedWildcard.extendsBound(type)
                : ResolvedWildcard.superBound(type);
    }

    private Set<ResolvedType> toSet(ResolvedType... resolvedTypes) {
        return new HashSet<>(Arrays.asList(resolvedTypes));
    }
}
