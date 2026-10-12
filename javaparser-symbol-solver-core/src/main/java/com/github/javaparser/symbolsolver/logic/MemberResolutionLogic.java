/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2026 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.logic;

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.resolution.Context;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.HasAccessSpecifier;
import com.github.javaparser.resolution.declarations.ResolvedEnumDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.logic.MethodResolutionLogic;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.ResolvedTypeVariable;
import com.github.javaparser.symbolsolver.core.resolution.TypeVariableResolutionCapability;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Function;
import java.util.stream.Collectors;

/**
 * Looks up members of a type: the methods it declares plus the ones it inherits from its ancestors.
 * <p>
 * This is deliberately narrower than a lexical lookup. A member lookup answers "does this type have
 * such a member?", so it stops at the type and its hierarchy; it never consults the compilation unit
 * the type happens to be declared in, because imports are a property of that file and not members of
 * the type (JLS 7.5.3, 7.5.4).
 *
 * @author Federico Tomassetti
 */
public class MemberResolutionLogic {

    private MemberResolutionLogic() {
        // This class is meant to be used statically only.
    }

    /**
     * Recursively checks the ancestors of the {@param declaration} if an internal type is declared with a name equal
     * to {@param name}.
     * TODO: Edit to remove return of null (favouring a return of optional)
     * @return A ResolvedTypeDeclaration matching the {@param name}, null otherwise
     */
    public static ResolvedTypeDeclaration checkAncestorsForType(
            String name, ResolvedReferenceTypeDeclaration declaration) {
        for (ResolvedReferenceType ancestor : declaration.getAncestors(true)) {
            try {
                // TODO: Figure out if it is appropriate to remove the orElseThrow() -- if so, how...
                ResolvedReferenceTypeDeclaration ancestorReferenceTypeDeclaration = ancestor.getTypeDeclaration()
                        .orElseThrow(() -> new RuntimeException("TypeDeclaration unexpectedly empty."));

                for (ResolvedTypeDeclaration internalTypeDeclaration :
                        ancestorReferenceTypeDeclaration.internalTypes()) {
                    boolean visible = true;
                    if (internalTypeDeclaration instanceof ResolvedReferenceTypeDeclaration) {
                        ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration =
                                internalTypeDeclaration.asReferenceType();
                        if (resolvedReferenceTypeDeclaration instanceof HasAccessSpecifier) {
                            visible = ((HasAccessSpecifier) resolvedReferenceTypeDeclaration).accessSpecifier()
                                    != AccessSpecifier.PRIVATE;
                        }
                    }
                    if (internalTypeDeclaration.getName().equals(name)) {
                        if (visible) {
                            return internalTypeDeclaration;
                        }
                        return null;
                    }
                }

                // check recursively the ancestors of this ancestor
                ResolvedTypeDeclaration ancestorTypeDeclaration =
                        checkAncestorsForType(name, ancestorReferenceTypeDeclaration);
                if (ancestorTypeDeclaration != null) {
                    return ancestorTypeDeclaration;
                }
            } catch (UnsupportedOperationException e) {
                // just continue using the next ancestor
            }
        }
        return null; // FIXME -- Avoid returning null.
    }

    /**
     * Solves a type among the members of {@code typeDeclaration}: the types it declares and the ones it
     * inherits, and nothing else. A composite name such as {@code Outer.Inner} is resolved one member at
     * a time, each step staying within the members of the type the previous one found.
     */
    public static SymbolReference<ResolvedTypeDeclaration> solveTypeInMembers(
            ResolvedTypeDeclaration typeDeclaration, String name) {

        int firstDot = name.indexOf('.');
        if (firstDot > -1) {
            SymbolReference<ResolvedTypeDeclaration> outer =
                    solveTypeInMembers(typeDeclaration, name.substring(0, firstDot));
            if (!outer.isSolved()) {
                return SymbolReference.unsolved();
            }
            return solveTypeInMembers(outer.getCorrespondingDeclaration(), name.substring(firstDot + 1));
        }

        for (ResolvedReferenceTypeDeclaration internalType : typeDeclaration.internalTypes()) {
            if (internalType.getName().equals(name)) {
                return SymbolReference.solved(internalType);
            }
        }

        if (typeDeclaration.isReferenceType()) {
            ResolvedTypeDeclaration inherited = checkAncestorsForType(name, typeDeclaration.asReferenceType());
            if (inherited != null) {
                return SymbolReference.solved(inherited);
            }
        }

        return SymbolReference.unsolved();
    }

    /**
     * Solves a value among the members of {@code typeDeclaration}: its enum constants, then the fields it
     * declares and the ones it inherits, and nothing else.
     */
    public static SymbolReference<? extends ResolvedValueDeclaration> solveSymbolInMembers(
            ResolvedReferenceTypeDeclaration typeDeclaration, String name) {

        if (typeDeclaration.isEnum()) {
            // Enum constants are members of the enum, and no field declaration declares them.
            ResolvedEnumDeclaration enumDeclaration = typeDeclaration.asEnum();
            if (enumDeclaration.hasEnumConstant(name)) {
                return SymbolReference.solved(enumDeclaration.getEnumConstant(name));
            }
        }

        if (typeDeclaration.hasVisibleField(name)) {
            return SymbolReference.solved(typeDeclaration.getVisibleField(name));
        }

        return SymbolReference.unsolved();
    }

    /**
     * Collects the methods named {@code name} that {@code typeDeclaration} declares or inherits.
     *
     * @return a mutable list, so that callers can keep adding candidates of their own.
     */
    public static List<ResolvedMethodDeclaration> collectCandidateMembers(
            ResolvedReferenceTypeDeclaration typeDeclaration,
            String name,
            List<ResolvedType> argumentsTypes,
            boolean staticOnly) {

        // Begin by locating methods declared "here"
        List<ResolvedMethodDeclaration> candidateMethods = typeDeclaration.getDeclaredMethods().stream()
                .filter(m -> m.getName().equals(name))
                .filter(m -> !staticOnly || m.isStatic())
                .collect(Collectors.toCollection(ArrayList::new));

        // Next, consider methods declared within ancestors.
        // Note that we only consider ancestors when we are not currently at java.lang.Object (avoiding infinite
        // recursion).
        if (!typeDeclaration.isJavaLangObject()) {
            for (ResolvedReferenceType ancestor : typeDeclaration.getAncestors(true)) {
                Optional<ResolvedReferenceTypeDeclaration> ancestorTypeDeclaration = ancestor.getTypeDeclaration();

                // Avoid recursion on self
                if (ancestorTypeDeclaration.isPresent() && typeDeclaration != ancestorTypeDeclaration.get()) {
                    // Consider the methods of the ancestor and of its own ancestors. They are only collected here:
                    // resolving the call on the ancestor itself would compare them on its raw declaration, where
                    // overloads such as set(T) and set(U) cannot be told apart, instead of comparing them with
                    // the others on their parameter types as seen from typeDeclaration (see parameterTypesSeenFrom).
                    candidateMethods.addAll(ancestor.getAllMethodsVisibleToInheritors().stream()
                            .filter(m -> m.getName().equals(name))
                            .collect(Collectors.toList()));
                }
            }
        }

        return candidateMethods;
    }

    /**
     * Solves a method among the members of {@code typeDeclaration}: the ones it declares and the ones it
     * inherits, and nothing else.
     */
    public static SymbolReference<ResolvedMethodDeclaration> solveMethodInMembers(
            ResolvedReferenceTypeDeclaration typeDeclaration,
            String name,
            List<ResolvedType> argumentsTypes,
            boolean staticOnly,
            TypeSolver typeSolver) {
        return solveMethodInMembers(
                typeDeclaration, name, argumentsTypes, staticOnly, Collections.emptyList(), typeSolver);
    }

    /**
     * Same as {@link #solveMethodInMembers(ResolvedReferenceTypeDeclaration, String, List, boolean, TypeSolver)},
     * for a call on a receiver that supplies {@code typeArguments} for the type parameters of
     * {@code typeDeclaration}.
     */
    public static SymbolReference<ResolvedMethodDeclaration> solveMethodInMembers(
            ResolvedReferenceTypeDeclaration typeDeclaration,
            String name,
            List<ResolvedType> argumentsTypes,
            boolean staticOnly,
            List<ResolvedType> typeArguments,
            TypeSolver typeSolver) {

        List<ResolvedMethodDeclaration> candidateMethods =
                collectCandidateMembers(typeDeclaration, name, argumentsTypes, staticOnly);

        // if is interface and candidate method list is empty, we should check the Object Methods
        if (candidateMethods.isEmpty() && typeDeclaration.isInterface()) {
            SymbolReference<ResolvedMethodDeclaration> res = MethodResolutionLogic.solveMethodInType(
                    typeSolver.getSolvedJavaLangObject(), name, argumentsTypes, false);
            if (res.isSolved()) {
                candidateMethods.add(res.getCorrespondingDeclaration());
            }
        }

        // The candidates are compared on their parameter types as seen from the receiver, so that the overloads
        // that only differ by type variables of their declaring type can be told apart
        return MethodResolutionLogic.findMostApplicable(
                candidateMethods,
                name,
                argumentsTypes,
                typeSolver,
                parameterTypesSeenFrom(typeDeclaration, typeArguments));
    }

    /**
     * Same as {@link #parameterTypesSeenFrom(ResolvedReferenceTypeDeclaration, List)}, for a lookup made from
     * within {@code typeDeclaration}, where its own type variables stand for themselves.
     */
    public static Function<ResolvedMethodDeclaration, List<ResolvedType>> parameterTypesSeenFrom(
            ResolvedReferenceTypeDeclaration typeDeclaration) {
        return parameterTypesSeenFrom(typeDeclaration, Collections.emptyList());
    }

    /**
     * Gives the parameter types of a candidate method as seen from a receiver of type {@code typeDeclaration}
     * parameterized with {@code typeArguments}: the type variables of the declaring type are replaced by the
     * type arguments that the receiver and its hierarchy supply for them, as in {@code set(T)} seen as
     * {@code set(String)} on a {@code Box<String>} or from a type that {@code extends Box<String>}.
     * <p>
     * Only the type variables declared on a type are replaced, never those declared on the method itself, which
     * are inferred from the arguments of the call. A type variable for which no type argument is known, such as
     * {@code T} on a {@code Box<? extends A, B>} whose type argument for {@code T} is a wildcard (see
     * {@link #receiverType}), is left in place and keeps accepting any argument.
     * <p>
     * The returned function is meant for a single lookup: it remembers the hierarchy of the receiver once walked.
     * <p>
     * Limitation: an ancestor declared as a raw type, as in {@code class Sub extends Base}, supplies no type
     * argument, so the type variables of its methods are left in place. javac compares such methods on their
     * erasure (JLS 4.8), {@code set(Object)} and {@code set(A)} for {@code set(U)} and {@code set(T extends A)},
     * whereas they still look equally applicable here, and the call stays ambiguous.
     */
    public static Function<ResolvedMethodDeclaration, List<ResolvedType>> parameterTypesSeenFrom(
            ResolvedReferenceTypeDeclaration typeDeclaration, List<ResolvedType> typeArguments) {
        // The receiver and each of its ancestors, by qualified name, with the type arguments the receiver
        // supplies to them: for a receiver Sub that extends Mid<String>, which extends Base<String, Long>, it maps
        // Mid to Mid<String> and Base to Base<String, Long>.
        Map<String, ResolvedReferenceType> typesByName = new HashMap<>();
        return method -> {
            List<ResolvedType> parameterTypes = new ArrayList<>(method.getNumberOfParams());
            for (int i = 0; i < method.getNumberOfParams(); i++) {
                parameterTypes.add(method.getParam(i).getType());
            }
            // A non generic declaring type has no type variable of its own that the receiver could bind
            ResolvedReferenceTypeDeclaration declaringType = method.declaringType();
            if (declaringType.getTypeParameters().isEmpty()) {
                return parameterTypes;
            }
            // The hierarchy is only walked once a candidate needs it, which most lookups never do
            if (typesByName.isEmpty()) {
                ResolvedReferenceType receiverType = receiverType(typeDeclaration, typeArguments);
                typesByName.put(typeDeclaration.getQualifiedName(), receiverType);
                collectResolvableAncestors(receiverType, typesByName);
            }
            // The declaring type as the receiver sees it, e.g. Base<String, Long> for a method of Base<T, U>.
            // It is missing when the method comes from an ancestor that could not be resolved, in which case
            // the declared types are kept.
            ResolvedReferenceType seenFrom = typesByName.get(declaringType.getQualifiedName());
            if (seenFrom != null) {
                // Replaces T and U, also inside types such as List<T> or ? super U, by String and Long
                parameterTypes.replaceAll(seenFrom::useThisTypeParametersOnTheGivenType);
            }
            return parameterTypes;
        };
    }

    /**
     * The receiver {@code typeDeclaration<typeArguments>}. Without a type argument for each type parameter, as
     * for a raw type or a lookup from within the type, the type variables stand for themselves. So does a type
     * variable whose type argument is a wildcard, such as {@code T} on a {@code Box<? extends Number, B>}: the
     * wildcard is not substituted for it, since a parameter of type {@code ? extends Number} accepts no argument
     * other than {@code null}, which would make the method inapplicable where javac captures the wildcard.
     * <p>
     * Limitations:
     * <ul>
     *   <li>A raw receiver is not erased (JLS 4.8): its type variables stand for themselves, so overloads such as
     *   {@code set(T)} and {@code set(U)} stay ambiguous on it, where javac compares their erasures.</li>
     *   <li>Leaving in place a type variable whose type argument is a wildcard only approximates capture
     *   conversion (JLS 5.1.10). It accepts at least the arguments that javac accepts, but may rank the overloads
     *   differently: on a {@code Box<? extends A, B>}, the call {@code set(null)} resolves to {@code set(U)}
     *   because {@code B} is more specific than the type variable {@code T}, whereas javac selects
     *   {@code set(T)}.</li>
     *   <li>{@code typeArguments} are trusted to be the type arguments of {@code typeDeclaration}; only their
     *   number is checked. The Reflection and Javassist declarations hand the type arguments of their own
     *   receiver to the lookup in each of their ancestors. Should such an ancestor be a JavaParser declaration
     *   with as many type parameters, these type arguments would be applied to it as if they were its own.</li>
     * </ul>
     */
    private static ResolvedReferenceType receiverType(
            ResolvedReferenceTypeDeclaration typeDeclaration, List<ResolvedType> typeArguments) {
        List<ResolvedTypeParameterDeclaration> typeParameters = typeDeclaration.getTypeParameters();
        // No type argument at all (raw type, lookup from within the type, non generic type) or an unexpected
        // number of them: each type variable is bound to itself, so that only the ancestors' type arguments,
        // which the type declares in its extends and implements clauses, are substituted
        if (typeArguments.size() != typeParameters.size()) {
            return ReferenceTypeImpl.undeterminedParameters(typeDeclaration);
        }
        List<ResolvedType> knownTypeArguments = new ArrayList<>(typeArguments.size());
        for (int i = 0; i < typeArguments.size(); i++) {
            ResolvedType typeArgument = typeArguments.get(i);
            // A wildcard type argument is not substituted: the type variable it is given for is kept, and accepts
            // any argument, as when nothing is known about the receiver
            knownTypeArguments.add(
                    typeArgument.isWildcard() ? new ResolvedTypeVariable(typeParameters.get(i)) : typeArgument);
        }
        return new ReferenceTypeImpl(typeDeclaration, knownTypeArguments);
    }

    /**
     * Collects the ancestors of {@code type}, direct and indirect, with the type arguments its hierarchy
     * supplies, leaving out the ones that cannot be resolved together with their own ancestors.
     * <p>
     * Each step goes through {@link ResolvedReferenceType#getDirectAncestors(boolean)}, which expresses the type
     * arguments of an ancestor in terms of those of {@code type}: from {@code Mid<String>}, the ancestor declared
     * as {@code Base<K, Long>} is returned as {@code Base<String, Long>}. Passing {@code true} tolerates
     * ancestors that cannot be resolved, as {@code getAllMethodsVisibleToInheritors} does when collecting the
     * candidates, so that both walk the same hierarchy.
     */
    private static void collectResolvableAncestors(
            ResolvedReferenceType type, Map<String, ResolvedReferenceType> ancestorsByName) {
        for (ResolvedReferenceType ancestor : type.getDirectAncestors(true)) {
            // Guard against cyclic hierarchies, which incomplete or erroneous sources may contain
            if (ancestorsByName.putIfAbsent(ancestor.getQualifiedName(), ancestor) == null) {
                collectResolvableAncestors(ancestor, ancestorsByName);
            }
        }
    }

    /**
     * Solves a method among the members of {@code typeDeclaration} and resolves its type variables, so that
     * the result can be used as a {@link MethodUsage}.
     *
     * @param context the context the resulting usage is resolved against; it is not searched for candidates.
     */
    public static Optional<MethodUsage> solveMethodAsUsageInMembers(
            ResolvedReferenceTypeDeclaration typeDeclaration,
            String name,
            List<ResolvedType> argumentsTypes,
            Context context,
            TypeSolver typeSolver) {
        return solveMethodAsUsageInMembers(
                typeDeclaration, name, argumentsTypes, context, Collections.emptyList(), typeSolver);
    }

    /**
     * Same as
     * {@link #solveMethodAsUsageInMembers(ResolvedReferenceTypeDeclaration, String, List, Context, TypeSolver)},
     * for a call on a receiver that supplies {@code typeArguments} for the type parameters of
     * {@code typeDeclaration}.
     */
    public static Optional<MethodUsage> solveMethodAsUsageInMembers(
            ResolvedReferenceTypeDeclaration typeDeclaration,
            String name,
            List<ResolvedType> argumentsTypes,
            Context context,
            List<ResolvedType> typeArguments,
            TypeSolver typeSolver) {

        // The receiver's type arguments only select the method; the usage is then built from the selected
        // declaration, as before, the caller substituting the receiver's type arguments into it
        SymbolReference<ResolvedMethodDeclaration> methodSolved =
                solveMethodInMembers(typeDeclaration, name, argumentsTypes, false, typeArguments, typeSolver);
        if (!methodSolved.isSolved()) {
            return Optional.empty();
        }

        ResolvedMethodDeclaration methodDeclaration = methodSolved.getCorrespondingDeclaration();
        if (!(methodDeclaration instanceof TypeVariableResolutionCapability)) {
            throw new UnsupportedOperationException(String.format(
                    "Resolved method declarations must implement %s.",
                    TypeVariableResolutionCapability.class.getName()));
        }
        return Optional.of(
                ((TypeVariableResolutionCapability) methodDeclaration).resolveTypeVariables(context, argumentsTypes));
    }
}
