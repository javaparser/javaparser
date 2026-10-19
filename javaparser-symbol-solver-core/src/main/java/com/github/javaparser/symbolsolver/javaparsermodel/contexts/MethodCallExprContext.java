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

package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import static com.github.javaparser.resolution.Navigator.demandParentNode;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.RecordDeclaration;
import com.github.javaparser.ast.expr.EnclosedExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.MethodReferenceExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.resolution.Context;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.logic.FunctionalInterfaceLogic;
import com.github.javaparser.resolution.logic.MethodResolutionLogic;
import com.github.javaparser.resolution.model.LambdaArgumentTypePlaceholder;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.model.typesystem.LazyType;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.*;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.resolution.typeinference.LeastUpperBoundLogic;
import com.github.javaparser.utils.Pair;
import java.util.*;
import java.util.stream.Collectors;

public class MethodCallExprContext extends ExpressionContext<MethodCallExpr> {

    ///
    /// Constructors
    ///

    public MethodCallExprContext(MethodCallExpr wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    ///
    /// Public methods
    ///

    @Override
    public Optional<ResolvedType> solveGenericType(String name) {
        Optional<Expression> nodeScope = wrappedNode.getScope();
        if (!nodeScope.isPresent()) {
            return Optional.empty();
        }

        // Method calls can have generic types defined, for example: {@code expr.<T1, T2>method(x, y, z);} or {@code
        // super.<T, E>check2(val1, val2).}
        ResolvedType typeOfScope = JavaParserFacade.get(typeSolver).getType(nodeScope.get());
        Optional<ResolvedType> resolvedType = typeOfScope.asReferenceType().getGenericParameterByName(name);

        // TODO/FIXME: Consider if we should check if the result is present, else delegate "up" the context chain (e.g.
        // {@code solveGenericTypeInParent()})
        return resolvedType;
    }

    @Override
    public String toString() {
        return "MethodCallExprContext{wrapped=" + wrappedNode + "}";
    }

    @Override
    public Optional<MethodUsage> solveMethodAsUsage(String name, List<ResolvedType> argumentsTypes) {
        ResolvedType typeOfScope;
        if (wrappedNode.hasScope()) {
            Expression scope = wrappedNode.getScope().get();
            // Consider static method calls
            if (scope instanceof NameExpr) {
                String className = ((NameExpr) scope).getName().getId();
                SymbolReference<ResolvedTypeDeclaration> ref = solveType(className);
                if (ref.isSolved()) {
                    SymbolReference<ResolvedMethodDeclaration> m = MethodResolutionLogic.solveMethodInType(
                            ref.getCorrespondingDeclaration(), name, argumentsTypes);
                    if (m.isSolved()) {
                        MethodUsage methodUsage = new MethodUsage(m.getCorrespondingDeclaration());
                        methodUsage = resolveMethodTypeParametersFromExplicitList(typeSolver, methodUsage);
                        methodUsage = resolveMethodTypeParameters(methodUsage, argumentsTypes);
                        // Phase 2 (JLS §15.12.2.7): infer remaining type variables from poly
                        // expression arguments (method/constructor references).
                        methodUsage = inferTypeVariablesFromPolyExpressionArguments(methodUsage, argumentsTypes);
                        return Optional.of(methodUsage);
                    }
                    throw new UnsolvedSymbolException(
                            ref.getCorrespondingDeclaration().toString(),
                            "Method '" + name + "' with parameterTypes " + argumentsTypes);
                }
            }

            // Scope is present -- search/solve within that type
            typeOfScope = JavaParserFacade.get(typeSolver).getType(scope);
        } else {
            // Scope not present -- search/solve within itself.
            typeOfScope = JavaParserFacade.get(typeSolver).getTypeOfThisIn(wrappedNode);
        }

        // we can replace the parameter types from the scope into the typeParametersValues
        Map<ResolvedTypeParameterDeclaration, ResolvedType> inferredTypes = new HashMap<>();
        for (int i = 0; i < argumentsTypes.size(); i++) {
            // by replacing types I can also find new equivalences
            // for example if I replace T=U with String because I know that T=String I can derive that also U equal
            // String
            ResolvedType originalArgumentType = argumentsTypes.get(i);
            ResolvedType updatedArgumentType =
                    usingParameterTypesFromScope(typeOfScope, originalArgumentType, inferredTypes);
            argumentsTypes.set(i, updatedArgumentType);
        }
        for (int i = 0; i < argumentsTypes.size(); i++) {
            ResolvedType updatedArgumentType = applyInferredTypes(argumentsTypes.get(i), inferredTypes);
            argumentsTypes.set(i, updatedArgumentType);
        }

        Optional<MethodUsage> ref = solveMethodAsUsage(typeOfScope, name, argumentsTypes, this);
        if (!ref.isPresent() && !wrappedNode.hasScope()) {
            // A call without a receiver is a lexical lookup, so when the type it is written in has no such
            // member the enclosing scopes still apply -- including that file's static imports. See
            // solveMethod for why this starts at the enclosing type rather than at the parent context.
            ref = JavaParserFactory.getContext(enclosingTypeOf(wrappedNode), typeSolver)
                    .solveMethodAsUsage(name, argumentsTypes);
        }
        return ref;
    }

    /**
     * The node whose type provides {@code this} for a call written at {@code node}: the type declaration
     * enclosing it, or the anonymous class body it is written in. The compilation unit acts as the stop
     * condition for a call written outside any type.
     */
    private static Node enclosingTypeOf(Node node) {
        Node parent = demandParentNode(node);
        if (parent instanceof ClassOrInterfaceDeclaration
                || parent instanceof RecordDeclaration
                || parent instanceof EnumDeclaration
                || parent instanceof CompilationUnit
                || (parent instanceof ObjectCreationExpr
                        && ((ObjectCreationExpr) parent).getAnonymousClassBody().isPresent())) {
            return parent;
        }
        return enclosingTypeOf(parent);
    }

    private MethodUsage resolveMethodTypeParametersFromExplicitList(TypeSolver typeSolver, MethodUsage methodUsage) {
        if (wrappedNode.getTypeArguments().isPresent()) {
            final List<ResolvedType> typeArguments = new ArrayList<>();
            for (com.github.javaparser.ast.type.Type ty :
                    wrappedNode.getTypeArguments().get()) {
                typeArguments.add(JavaParserFacade.get(typeSolver).convertToUsage(ty));
            }

            List<ResolvedTypeParameterDeclaration> tyParamDecls =
                    methodUsage.getDeclaration().getTypeParameters();
            if (tyParamDecls.size() == typeArguments.size()) {
                for (int i = 0; i < tyParamDecls.size(); i++) {
                    methodUsage = methodUsage.replaceTypeParameter(tyParamDecls.get(i), typeArguments.get(i));
                }
            }
        }

        return methodUsage;
    }

    @Override
    public SymbolReference<ResolvedMethodDeclaration> solveMethod(
            String name, List<ResolvedType> argumentsTypes, boolean staticOnly) {
        // A call without a receiver is a lexical lookup, not a member lookup: besides the members of the
        // type it is written in, it can reach the enclosing types and that file's static imports. Start it
        // at the enclosing type, whose context searches exactly those, rather than at the parent context:
        // the expressions a call is nested in resolve calls of their own and do not relay such a lookup.
        if (!wrappedNode.hasScope()) {
            return JavaParserFactory.getContext(enclosingTypeOf(wrappedNode), typeSolver)
                    .solveMethod(name, argumentsTypes, staticOnly);
        }

        // The receiver is kept with its type arguments, not reduced to its declaration: on a Box<String>, they tell
        // set(T) apart from an overload set(U) once T and U are bound to different types.
        // Limitation: only the JavaParser declarations use them. A receiver whose type comes from Reflection or
        // Javassist (a JDK or library class) is still resolved on its declared signatures.
        Collection<ResolvedReferenceType> receiverTypes = findReceiverTypes(wrappedNode.getScope());

        if (receiverTypes.isEmpty()) {
            // if the bounds of a type parameter are empty, then the bound is implicitly "extends Object"
            // we don't make this _ex_plicit in the data representation because that would affect codegen
            // and make everything generate like <T extends Object> instead of <T>
            // https://github.com/javaparser/javaparser/issues/2044
            receiverTypes = Collections.singleton(new ReferenceTypeImpl(typeSolver.getSolvedJavaLangObject()));
        }

        for (ResolvedReferenceType receiverType : receiverTypes) {
            SymbolReference<ResolvedMethodDeclaration> res =
                    MethodResolutionLogic.solveMethodInType(receiverType, name, argumentsTypes, false);
            if (res.isSolved()
                    && !hasIncompatibleCaptureArgument(
                            receiverType, res.getCorrespondingDeclaration(), argumentsTypes)) {
                return res;
            }
        }

        return SymbolReference.unsolved();
    }

    ///
    /// Private methods
    ///

    private boolean hasIncompatibleCaptureArgument(
            ResolvedReferenceType receiver, ResolvedMethodDeclaration method, List<ResolvedType> arguments) {
        for (int i = 0; i < arguments.size(); i++) {
            int parameterIndex = Math.min(i, method.getNumberOfParams() - 1);
            if (parameterIndex < 0) {
                break;
            }
            ResolvedType parameter = receiver.useThisTypeParametersOnTheGivenType(
                    method.getParam(parameterIndex).getType());
            if (method.getParam(parameterIndex).isVariadic() && parameter.isArray()) {
                parameter = parameter.asArrayType().getComponentType();
                if (i == parameterIndex
                        && arguments.size() == method.getNumberOfParams()
                        && arguments.get(i).isArray()
                        && parameter.isAssignableBy(
                                arguments.get(i).asArrayType().getComponentType())) {
                    continue;
                }
            }
            if (ResolvedCaptureType.containsCapture(parameter) && !parameter.isAssignableBy(arguments.get(i))) {
                return true;
            }
        }
        return false;
    }

    private boolean containsSuperWildcard(ResolvedType type) {
        if (type.isWildcard()) {
            return type.asWildcard().isSuper()
                    || (type.asWildcard().isBounded()
                            && containsSuperWildcard(type.asWildcard().getBoundedType()));
        }
        if (type.isArray()) {
            return containsSuperWildcard(type.asArrayType().getComponentType());
        }
        return type.isReferenceType()
                && type.asReferenceType().typeParametersValues().stream().anyMatch(this::containsSuperWildcard);
    }

    private Optional<MethodUsage> solveMethodAsUsage(
            ResolvedReferenceType refType, String name, List<ResolvedType> argumentsTypes, Context invokationContext) {
        if (!refType.getTypeDeclaration().isPresent()) {
            return Optional.empty();
        }

        Optional<MethodUsage> ref = ContextHelper.solveMethodAsUsage(
                refType.getTypeDeclaration().get(),
                name,
                argumentsTypes,
                invokationContext,
                refType.typeParametersValues());
        if (ref.isPresent()) {
            MethodUsage methodUsage = ref.get();
            if (hasIncompatibleCaptureArgument(refType, methodUsage.getDeclaration(), argumentsTypes)) {
                return Optional.empty();
            }

            if (!methodUsage.getDeclaration().getTypeParameters().isEmpty()
                    && argumentsTypes.stream().anyMatch(this::containsSuperWildcard)) {
                // The declaration-level inference may have already replaced a super capture by
                // its lower bound. Re-infer from the declared return type, using the same
                // constraints as static calls, before the legacy substitution pass below.
                methodUsage = new MethodUsage(
                        methodUsage.getDeclaration(),
                        methodUsage.getParamTypes().stream()
                                .map(refType::useThisTypeParametersOnTheGivenType)
                                .collect(Collectors.toList()),
                        refType.useThisTypeParametersOnTheGivenType(
                                methodUsage.getDeclaration().getReturnType()));
                methodUsage = resolveMethodTypeParametersFromExplicitList(typeSolver, methodUsage);
                methodUsage = resolveMethodTypeParameters(methodUsage, argumentsTypes);
            } else {
                methodUsage = resolveMethodTypeParametersFromExplicitList(typeSolver, methodUsage);
            }

            // At this stage I should derive from the context and the value some information on the type parameters
            // for example, when calling:
            // myStream.collect(Collectors.toList())
            // I should be able to figure out that considering the type of the stream (e.g., Stream<String>)
            // and considering that Stream has this method:
            //
            // <R,A> R collect(Collector<? super T,A,R> collector)
            //
            // and collector has this method:
            //
            // static <T> Collector<T,?,List<T>>   toList()
            //
            // In this case collect.R has to be equal to List<toList.T>
            // And toList.T has to be equal to ? super Stream.T
            // Therefore R has to be equal to List<? super Stream.T>.
            // In our example Stream.T equal to String, so the R (and the result of the call to collect) is
            // List<? super String>

            Map<ResolvedTypeParameterDeclaration, ResolvedType> derivedValues = new HashMap<>();
            for (int i = 0; i < methodUsage.getParamTypes().size(); i++) {
                ResolvedParameterDeclaration parameter =
                        methodUsage.getDeclaration().getParam(i);
                ResolvedType parameterType = parameter.getType();
                // Don't continue if a vararg parameter is reached and there are no arguments left
                if (parameter.isVariadic() && argumentsTypes.size() < methodUsage.getNoParams()) {
                    break;
                }
                if (!argumentsTypes.get(i).isArray() && parameter.isVariadic()) {
                    parameterType = parameterType.asArrayType().getComponentType();
                }
                MethodResolutionLogic.inferTypes(argumentsTypes.get(i), parameterType, derivedValues);
            }

            for (Map.Entry<ResolvedTypeParameterDeclaration, ResolvedType> entry : derivedValues.entrySet()) {
                methodUsage = methodUsage.replaceTypeParameter(entry.getKey(), entry.getValue());
            }

            // Phase 2 (JLS §15.12.2.7): infer remaining type variables from poly-expression
            // arguments (method/constructor references).  After Phase 1 some type variables may
            // still be unresolved (e.g. K in groupingBy(Function<? super T, ? extends K>, ...)).
            // For each argument that was a method/constructor reference, we derive the actual
            // return type of the referenced callable and match it against the SAM's formal return
            // type to produce additional bindings.  Lambdas are skipped — their return type is
            // itself context-dependent and cannot be resolved here without full poly-expression
            // inference.
            methodUsage = inferTypeVariablesFromPolyExpressionArguments(methodUsage, argumentsTypes);

            ResolvedType returnType = refType.useThisTypeParametersOnTheGivenType(methodUsage.returnType());
            // we don't want to replace the return type in case of UNBOUNDED type (<?>)
            if (returnType != methodUsage.returnType() && !(returnType == ResolvedWildcard.UNBOUNDED)) {
                methodUsage = methodUsage.replaceReturnType(returnType);
            }
            for (int i = 0; i < methodUsage.getParamTypes().size(); i++) {
                ResolvedType replaced = refType.useThisTypeParametersOnTheGivenType(
                        methodUsage.getParamTypes().get(i));
                methodUsage = methodUsage.replaceParamType(i, replaced);
            }
            return Optional.of(methodUsage);
        }
        return ref;
    }

    /**
     * Phase 2 of JLS §15.12.2.7 poly-expression type inference.
     *
     * <p>After Phase 1 has inferred type variables from concrete (non-poly) arguments, some
     * variables may still be unresolved — for example {@code K} in
     * {@code groupingBy(Function<? super T, ? extends K> classifier, ...)} when {@code classifier}
     * is a constructor or method reference.  This method performs a supplementary inference pass
     * over every argument position that was a method or constructor reference:
     *
     * <ol>
     *   <li>Determine the formal parameter type at that position in {@code methodUsage} (which
     *       already reflects Phase-1 substitutions, e.g. {@code Function<? super String, ? extends K>}).
     *   <li>Obtain the SAM of that functional interface type via
     *       {@link FunctionalInterfaceLogic#getFunctionalMethod}.</li>
     *   <li>Compute the <em>actual</em> return type of the referenced callable:
     *       <ul>
     *         <li>Constructor reference ({@code X::new}): the constructed type {@code X}.</li>
     *         <li>Method reference ({@code Foo::bar}): the declared return type of the matched
     *             method obtained via {@link JavaParserFacade#toMethodUsage}.</li>
     *       </ul>
     *   </li>
     *   <li>Match the SAM's formal return type (stripping any {@code ? extends} / {@code ? super}
     *       wrapper) against the actual return type to derive additional type-variable bindings.</li>
     * </ol>
     *
     * <p>Lambdas are <strong>not</strong> handled: their return type is itself context-dependent
     * and cannot be inferred without full poly-expression inference.
     *
     * @param methodUsage   the partially-resolved method usage (after Phase 1)
     * @param argumentsTypes the argument types as seen during method resolution; poly arguments
     *                       are represented by {@link LambdaArgumentTypePlaceholder}
     * @return a (possibly further refined) {@link MethodUsage} with additional type variables
     *         replaced by their inferred types
     */
    private MethodUsage inferTypeVariablesFromPolyExpressionArguments(
            MethodUsage methodUsage, List<ResolvedType> argumentsTypes) {
        NodeList<Expression> callArgs = wrappedNode.getArguments();
        if (callArgs == null || callArgs.isEmpty()) {
            return methodUsage;
        }

        // Determine how many positional (non-vararg) parameters to iterate over
        int paramCount = methodUsage.getDeclaration().hasVariadicParameter()
                ? methodUsage.getDeclaration().getNumberOfParams() - 1
                : methodUsage.getDeclaration().getNumberOfParams();

        Map<ResolvedTypeParameterDeclaration, ResolvedType> polyDerivedValues = new HashMap<>();

        for (int i = 0; i < Math.min(paramCount, Math.min(argumentsTypes.size(), callArgs.size())); i++) {
            // Identify poly-expression arguments directly from the AST: in solveMethodAsUsage,
            // method/constructor references are already resolved to their formal parameter type
            // (via getType(param, false)), so they do NOT appear as LambdaArgumentTypePlaceholder.
            // We therefore check the original AST node instead.
            Expression rawArg = callArgs.get(i);
            while (rawArg instanceof EnclosedExpr) {
                rawArg = ((EnclosedExpr) rawArg).getInner();
            }
            if (!rawArg.isMethodReferenceExpr()) {
                continue;
            }

            // Obtain the formal functional interface type with Phase-1 substitutions applied
            ResolvedType formalParamType = methodUsage.getParamType(i);
            Optional<MethodUsage> samOpt = FunctionalInterfaceLogic.getFunctionalMethod(formalParamType);
            if (!samOpt.isPresent()) {
                continue;
            }

            // getFunctionalMethod returns the SAM of the raw type declaration; substitute the
            // type arguments from formalParamType so that the SAM's return type reflects the
            // actual type arguments (e.g. "? extends K", not the raw "R").
            MethodUsage sam = samOpt.get();
            if (formalParamType.isReferenceType()) {
                for (Pair<ResolvedTypeParameterDeclaration, ResolvedType> typeParamEntry :
                        formalParamType.asReferenceType().getTypeParametersMap()) {
                    sam = sam.replaceTypeParameter(typeParamEntry.a, typeParamEntry.b);
                }
            }

            ResolvedType samReturnType = sam.returnType();
            if (samReturnType.isVoid()) {
                continue;
            }

            // Unwrap a bounded wildcard on the SAM return type so that matchTypeParameters can
            // bind the inner type variable.  E.g. "? extends K" → "K", "? super K" → "K".
            ResolvedType samReturnEffective = samReturnType;
            if (samReturnType.isWildcard() && samReturnType.asWildcard().isBounded()) {
                samReturnEffective = samReturnType.asWildcard().getBoundedType();
            }

            MethodReferenceExpr ref = rawArg.asMethodReferenceExpr();
            ResolvedType actualReturnType = null;

            if (ref.isConstructorReference()) {
                // Constructor reference X::new always returns the constructed type X
                try {
                    actualReturnType = ref.getScope().calculateResolvedType();
                } catch (Exception e) {
                    // Unable to resolve the constructed type — skip this argument
                }
            } else {
                // Method reference: resolve the actual method and use its declared return type.
                // Replace wildcard param types with their bounds before calling toMethodUsage so
                // that the method lookup can match the correct overload.
                try {
                    List<ResolvedType> samParamTypes = new ArrayList<>();
                    for (int j = 0; j < sam.getNoParams(); j++) {
                        ResolvedType pt = sam.getParamType(j);
                        if (pt.isWildcard() && pt.asWildcard().isBounded()) {
                            pt = pt.asWildcard().getBoundedType();
                        }
                        samParamTypes.add(pt);
                    }
                    actualReturnType = JavaParserFacade.get(typeSolver)
                            .toMethodUsage(ref, samParamTypes)
                            .returnType();
                } catch (Exception e) {
                    // Unable to resolve — skip this argument
                }
            }

            if (actualReturnType == null) {
                continue;
            }

            // Match the effective SAM return type against the actual return type to derive bindings
            try {
                matchTypeParameters(samReturnEffective, actualReturnType, polyDerivedValues);
            } catch (Exception e) {
                // Mismatch or unsupported combination — skip this argument
            }
        }

        for (Map.Entry<ResolvedTypeParameterDeclaration, ResolvedType> entry : polyDerivedValues.entrySet()) {
            methodUsage = methodUsage.replaceTypeParameter(entry.getKey(), entry.getValue());
        }
        return methodUsage;
    }

    private enum ConstraintKind {
        EQUALITY,
        LOWER,
        UPPER
    }

    private class TypeParameterConstraints {
        final Map<ResolvedTypeParameterDeclaration, ResolvedType> equalities;
        final Map<ResolvedTypeParameterDeclaration, Set<ResolvedType>> lowerBounds = new HashMap<>();
        final Map<ResolvedTypeParameterDeclaration, Set<ResolvedType>> upperBounds = new HashMap<>();

        TypeParameterConstraints(Map<ResolvedTypeParameterDeclaration, ResolvedType> equalities) {
            this.equalities = equalities;
        }

        void record(ResolvedTypeParameterDeclaration parameter, ResolvedType type, ConstraintKind kind) {
            if (kind == ConstraintKind.EQUALITY) {
                equalities.put(parameter, type);
            } else {
                Map<ResolvedTypeParameterDeclaration, Set<ResolvedType>> bounds =
                        kind == ConstraintKind.LOWER ? lowerBounds : upperBounds;
                bounds.computeIfAbsent(parameter, key -> new LinkedHashSet<>()).add(type);
            }
        }

        void resolve() {
            Set<ResolvedTypeParameterDeclaration> parameters = new LinkedHashSet<>(lowerBounds.keySet());
            parameters.addAll(upperBounds.keySet());
            for (ResolvedTypeParameterDeclaration parameter : parameters) {
                if (equalities.containsKey(parameter)) {
                    continue;
                }
                Set<ResolvedType> lowers = lowerBounds.getOrDefault(parameter, Collections.emptySet());
                ResolvedType inferred = lowers.isEmpty()
                        ? null
                        : LeastUpperBoundLogic.of(typeSolver).lub(lowers);
                if (inferred == null || inferred.isNull()) {
                    Set<ResolvedType> uppers =
                            new LinkedHashSet<>(upperBounds.getOrDefault(parameter, Collections.emptySet()));
                    for (ResolvedTypeParameterDeclaration.Bound bound : parameter.getBounds()) {
                        if (bound.isExtends()) {
                            uppers.add(bound.getType());
                        }
                    }
                    inferred = mostSpecificUpperBound(uppers);
                }
                equalities.put(parameter, inferred);
            }
            for (Map.Entry<ResolvedTypeParameterDeclaration, Set<ResolvedType>> entry : upperBounds.entrySet()) {
                ResolvedType inferred = equalities.get(entry.getKey());
                Set<ResolvedType> bounds = new LinkedHashSet<>(entry.getValue());
                for (ResolvedTypeParameterDeclaration.Bound bound :
                        entry.getKey().getBounds()) {
                    if (bound.isExtends() && !bound.getType().mention(Collections.singletonList(entry.getKey()))) {
                        bounds.add(bound.getType());
                    }
                }
                for (ResolvedType upper : bounds) {
                    // A caller's type variable is not an inference variable we may instantiate here.
                    // Concrete upper bounds still have to accommodate the chosen equality/lower bound.
                    if ((!upper.isTypeVariable() || upper instanceof ResolvedCaptureType)
                            && !(inferred instanceof ResolvedIntersectionType)
                            && !upper.isAssignableBy(inferred)) {
                        throw new UnsolvedSymbolException(
                                "Incompatible bounds for " + entry.getKey().getName());
                    }
                }
            }
        }
    }

    private ResolvedType mostSpecificUpperBound(Set<ResolvedType> bounds) {
        if (bounds.isEmpty()) {
            return new ReferenceTypeImpl(typeSolver.getSolvedJavaLangObject());
        }
        List<ResolvedType> minimal = new ArrayList<>();
        for (ResolvedType bound : bounds) {
            if (minimal.stream().anyMatch(existing -> bound.isAssignableBy(existing))) {
                continue;
            }
            minimal.removeIf(existing -> existing.isAssignableBy(bound));
            minimal.add(bound);
        }
        // Arrays cannot form an intersection with an unrelated array or reference type.
        // Compatible bounds such as String[] and Serializable were already reduced above.
        if (minimal.size() > 1 && minimal.stream().anyMatch(ResolvedType::isArray)) {
            throw new UnsolvedSymbolException("Incompatible array upper bounds: " + minimal);
        }
        // An intersection can have at most one unrelated class bound (JLS 4.4).
        long classBounds = minimal.stream()
                .filter(type -> type.isReferenceType()
                        && type.asReferenceType()
                                .getTypeDeclaration()
                                .map(ResolvedTypeDeclaration::isClass)
                                .orElse(false))
                .count();
        if (classBounds > 1) {
            throw new UnsolvedSymbolException("Incompatible upper bounds: " + minimal);
        }
        return minimal.size() == 1 ? minimal.get(0) : new ResolvedIntersectionType(minimal);
    }

    private boolean isAssignableForInference(ResolvedType expected, ResolvedType actual) {
        return expected.isAssignableBy(actual)
                || (expected.isReferenceType()
                        && actual.isReferenceType()
                        && MethodResolutionLogic.isAssignableMatchTypeParameters(
                                expected.asReferenceType(), actual.asReferenceType(), new HashMap<>()));
    }

    private MethodUsage resolveMethodTypeParameters(MethodUsage methodUsage, List<ResolvedType> actualParamTypes) {
        Map<ResolvedTypeParameterDeclaration, ResolvedType> matchedTypeParameters = new HashMap<>();
        TypeParameterConstraints constraints = new TypeParameterConstraints(matchedTypeParameters);

        if (methodUsage.getDeclaration().hasVariadicParameter()) {
            if (actualParamTypes.size() == methodUsage.getDeclaration().getNumberOfParams()) {
                // the varargs parameter is an Array, so extract the inner type
                ResolvedType expectedType = methodUsage
                        .getDeclaration()
                        .getLastParam()
                        .getType()
                        .asArrayType()
                        .getComponentType();
                // the varargs corresponding type can be either T or Array<T>
                // for example
                // Arrays.aslist(int[]{1}) must returns List<int[]>
                // but Arrays.aslist(String[]{""}) must returns List<String>
                // Arrays.asList() accept generic type T. Since Java generics work only on
                // reference types (object types), not on primitives, and int[] is an object
                // then Arrays.aslist(int[]{1}) returns List<int[]>
                ResolvedType lastActualParamType = actualParamTypes.get(actualParamTypes.size() - 1);
                ResolvedType actualType = lastActualParamType;
                if (lastActualParamType.isArray()) {
                    ResolvedType componentType =
                            lastActualParamType.asArrayType().getComponentType();
                    // in cases where, the expected type is assignable by the actual reference type of the array
                    // (Files.newInputStream(path, options) and options is a variadic argument of type OpenOption)
                    // or the expected type is a generic type (Arrays.asList(T... a)) and the component type of the
                    // array type is a reference type
                    // or the expected type is not a generic (IntStream.of(int... values)) and the component type is not
                    // a reference type
                    // then the actual type is the component type (in the example above 'int')
                    if ((!componentType.isPrimitive() && ResolvedTypeVariable.class.isInstance(expectedType))
                            || (!componentType.isReferenceType()
                                    && !ResolvedTypeVariable.class.isInstance(expectedType))
                            || (componentType.isReferenceType()
                                    && isAssignableForInference(expectedType, componentType))) {
                        actualType = lastActualParamType.asArrayType().getComponentType();
                    }
                }
                if (!isAssignableForInference(expectedType, actualType)) {
                    for (ResolvedTypeParameterDeclaration tp :
                            methodUsage.getDeclaration().getTypeParameters()) {
                        expectedType = MethodResolutionLogic.replaceTypeParam(expectedType, tp, typeSolver);
                    }
                }
                if (!isAssignableForInference(expectedType, actualType)) {
                    // ok, then it needs to be wrapped
                    throw new UnsupportedOperationException(String.format(
                            "Unable to resolve the type typeParametersValues in a MethodUsage. Expected type: %s, Actual type: %s. Method Declaration: %s. MethodUsage: %s",
                            expectedType, actualType, methodUsage.getDeclaration(), methodUsage));
                }
                // match only the varargs type
                matchTypeParameters(expectedType, actualType, constraints, ConstraintKind.LOWER);
            } else {
                // Collect every expanded vararg, including when fixed parameters precede it.
                // With no varargs, the fixed arguments can still constrain the return type.
                ResolvedType expectedType = methodUsage
                        .getDeclaration()
                        .getLastParam()
                        .getType()
                        .asArrayType()
                        .getComponentType();
                int firstVararg = methodUsage.getDeclaration().getNumberOfParams() - 1;
                for (int i = firstVararg; i < actualParamTypes.size(); i++) {
                    ResolvedType actualType = actualParamTypes.get(i);
                    if (!isAssignableForInference(expectedType, actualType)) {
                        throw new UnsupportedOperationException(String.format(
                                "Unable to resolve the type typeParametersValues in a MethodUsage. Expected type: %s, Actual type: %s. Method Declaration: %s. MethodUsage: %s",
                                expectedType, actualType, methodUsage.getDeclaration(), methodUsage));
                    }
                    matchTypeParameters(expectedType, actualType, constraints, ConstraintKind.LOWER);
                }
            }
        }

        int until = methodUsage.getDeclaration().hasVariadicParameter()
                ? methodUsage.getDeclaration().getNumberOfParams() - 1
                : actualParamTypes.size();

        for (int i = 0; i < until; i++) {
            ResolvedType expectedType = methodUsage.getParamType(i);
            ResolvedType actualType = actualParamTypes.get(i);
            // A direct argument of type S supplies S <: T. Invariant type arguments such as
            // List<T> supply equality constraints when reference-type matching recurses below.
            matchTypeParameters(expectedType, actualType, constraints, ConstraintKind.LOWER);
        }
        constraints.resolve();
        methodUsage = replaceTypeParameter(methodUsage, matchedTypeParameters);
        return methodUsage;
    }

    /*
     * Replace formal type parameter (e.g. T) by actual type argument
     * If there is more than one actual type argument for a formal type parameter
     * then the type parameter list is reduced using LUB fonction.
     */
    private MethodUsage replaceTypeParameter(
            MethodUsage methodUsage, Map<ResolvedTypeParameterDeclaration, ResolvedType> matchedTypeParameters) {
        // first group all resolved types by type variable
        Map<String, Set<ResolvedType>> resolvedTypesByTypeVariable =
                groupResolvedTypeByTypeVariable(matchedTypeParameters);
        // then reduce the list of resolved types with the least upper bound logic
        Map<String, ResolvedType> reducedResolvedTypesByTypeVariable =
                reduceResolvedTypesByTypeVariable(resolvedTypesByTypeVariable);
        // then replace resolved type by the reduced type for each type variable
        convertTypesParameters(matchedTypeParameters, reducedResolvedTypesByTypeVariable);
        // finally replace type parameters
        for (ResolvedTypeParameterDeclaration tp : matchedTypeParameters.keySet()) {
            methodUsage = methodUsage.replaceTypeParameter(tp, matchedTypeParameters.get(tp));
        }
        return methodUsage;
    }

    /*
     * Update the matchedTypeParameters map from the types in reducedResolvedTypesByTypeVariable map.
     */
    private void convertTypesParameters(
            Map<ResolvedTypeParameterDeclaration, ResolvedType> matchedTypeParameters,
            Map<String, ResolvedType> reducedResolvedTypesByTypeVariable) {
        for (ResolvedTypeParameterDeclaration tp : matchedTypeParameters.keySet()) {
            String typeParameterName = tp.getName();
            boolean replacement = reducedResolvedTypesByTypeVariable.keySet().contains(typeParameterName);
            if (replacement) {
                matchedTypeParameters.put(tp, reducedResolvedTypesByTypeVariable.get(typeParameterName));
            }
        }
    }

    /*
     * Group resolved type by the variable type. For example in Map.of("k0", 0, "k1",
     * 1D) which is solved as static <K, V> Map<K, V> of(K k1, V v1, K k2, V v2)
     * the type variable named V that represents the type of the first and fourth parameter
     * must reference v1 (Integer type) and v2 (Double type).
     */
    private Map<String, Set<ResolvedType>> groupResolvedTypeByTypeVariable(
            Map<ResolvedTypeParameterDeclaration, ResolvedType> typeParameters) {
        Map<String, Set<ResolvedType>> resolvedTypesByTypeVariable = new HashMap<>();
        for (ResolvedTypeParameterDeclaration tp : typeParameters.keySet()) {
            String typeParameterName = tp.getName();
            boolean alreadyCollected = resolvedTypesByTypeVariable.keySet().contains(typeParameterName);
            if (!alreadyCollected) {
                Set<ResolvedType> resolvedTypes = findResolvedTypesByTypeVariable(typeParameterName, typeParameters);
                resolvedTypesByTypeVariable.put(typeParameterName, resolvedTypes);
            }
        }
        return resolvedTypesByTypeVariable;
    }

    /*
     * Collect all resolved type from a type variable name
     */
    private Set<ResolvedType> findResolvedTypesByTypeVariable(
            String typeVariableName, Map<ResolvedTypeParameterDeclaration, ResolvedType> typeParameters) {
        return typeParameters.keySet().stream()
                .filter(resolvedTypeParameterDeclaration ->
                        resolvedTypeParameterDeclaration.getName().equals(typeVariableName))
                .map(resolvedTypeParameterDeclaration -> typeParameters.get(resolvedTypeParameterDeclaration))
                .collect(Collectors.toSet());
    }

    /*
     * Reduce all set of resolved type with LUB
     */
    private Map<String, ResolvedType> reduceResolvedTypesByTypeVariable(Map<String, Set<ResolvedType>> typeParameters) {
        Map<String, ResolvedType> reducedResolvedTypesList = new HashMap<>();
        for (String typeParameterName : typeParameters.keySet()) {
            ResolvedType type = reduceResolvedTypesWithLub(typeParameters.get(typeParameterName));
            reducedResolvedTypesList.put(typeParameterName, type);
        }
        return reducedResolvedTypesList;
    }

    private ResolvedType reduceResolvedTypesWithLub(Set<ResolvedType> resolvedTypes) {
        return LeastUpperBoundLogic.of(typeSolver).lub(resolvedTypes);
    }

    /** Collect equality, lower and upper constraints separately before choosing an instantiation. */
    private void matchTypeParameters(
            ResolvedType expectedType,
            ResolvedType actualType,
            Map<ResolvedTypeParameterDeclaration, ResolvedType> matchedTypeParameters) {
        TypeParameterConstraints constraints = new TypeParameterConstraints(matchedTypeParameters);
        matchTypeParameters(expectedType, actualType, constraints, ConstraintKind.LOWER);
        constraints.resolve();
    }

    private void matchTypeParameters(
            ResolvedType expectedType,
            ResolvedType actualType,
            TypeParameterConstraints constraints,
            ConstraintKind kind) {
        if (expectedType instanceof ResolvedCaptureType) {
            return; // A capture is a fixed existential type, not a method inference variable.
        }
        if (expectedType.isTypeVariable()) {
            ResolvedType type = actualType;
            if (type.isPrimitive()) {
                type = new ReferenceTypeImpl(
                        typeSolver.solveType(type.asPrimitive().getBoxTypeQName()));
            }
            if (type.isWildcard()) {
                ResolvedWildcard wildcard = type.asWildcard();
                if (wildcard.isSuper()) {
                    type = new ResolvedCaptureType(
                            wildcard,
                            Collections.singletonList(new ReferenceTypeImpl(typeSolver.getSolvedJavaLangObject())));
                } else if (wildcard.isExtends()) {
                    type = wildcard.getBoundedType();
                } else {
                    return;
                }
            }
            if (type.isTypeVariable()
                    && type.asTypeParameter()
                            .getQualifiedName()
                            .equals(expectedType.asTypeParameter().getQualifiedName())) {
                return;
            }
            constraints.record(expectedType.asTypeParameter(), type, kind);
        } else if (expectedType.isArray()) {
            if (actualType.isArray() || actualType.isNull()) {
                matchTypeParameters(
                        expectedType.asArrayType().getComponentType(),
                        actualType.isNull()
                                ? actualType
                                : actualType.asArrayType().getComponentType(),
                        constraints,
                        kind);
            }
        } else if (expectedType.isReferenceType()) {
            if (actualType.isTypeVariable()) {
                for (ResolvedTypeParameterDeclaration.Bound bound :
                        actualType.asTypeParameter().getBounds()) {
                    matchTypeParameters(expectedType, bound.getType(), constraints, kind);
                }
                return;
            }
            if (!actualType.isReferenceType()) {
                return;
            }
            ResolvedReferenceType expectedReference = expectedType.asReferenceType();
            ResolvedReferenceType actualReference = actualType.asReferenceType();
            if (actualReference.isRawType() || expectedReference.isRawType()) {
                return;
            }
            if (!actualReference.getQualifiedName().equals(expectedReference.getQualifiedName())) {
                // Capture before projecting onto an ancestor: the subclass may declare a
                // narrower upper bound than the ancestor's type parameter.
                List<ResolvedType> capturedArguments = new ArrayList<>();
                for (int i = 0; i < actualReference.typeParametersValues().size(); i++) {
                    capturedArguments.add(captureSuperArgument(actualReference, i));
                }
                actualReference = new ReferenceTypeImpl(
                        actualReference.getTypeDeclaration().get(), capturedArguments);
                // For T <: S (a super wildcard), align the formal subtype to the actual supertype.
                // For S <: T, align the actual subtype to the formal supertype.
                ResolvedReferenceType subtype = kind == ConstraintKind.UPPER ? expectedReference : actualReference;
                String superName = kind == ConstraintKind.UPPER
                        ? actualReference.getQualifiedName()
                        : expectedReference.getQualifiedName();
                Optional<ResolvedReferenceType> ancestor = subtype.getAllAncestors().stream()
                        .filter(type -> type.getQualifiedName().equals(superName))
                        .findFirst();
                if (!ancestor.isPresent()) {
                    return;
                }
                if (kind == ConstraintKind.UPPER) {
                    expectedReference = ancestor.get();
                } else {
                    actualReference = ancestor.get();
                }
            }
            List<ResolvedType> expectedArguments = expectedReference.typeParametersValues();
            List<ResolvedType> actualArguments = actualReference.typeParametersValues();
            if (actualArguments.isEmpty()) {
                return;
            }
            for (int i = 0; i < expectedArguments.size(); i++) {
                ResolvedType expectedArgument = expectedArguments.get(i);
                ResolvedType actualArgument = actualArguments.get(i);
                // A poly expression may still carry the formal wildcard itself. Capturing
                // that placeholder would freeze an inference variable before target typing.
                if (expectedArgument.isWildcard()
                        && actualArgument.isWildcard()
                        && expectedArgument.asWildcard().isBounded()
                        && actualArgument.asWildcard().isBounded()
                        && expectedArgument.asWildcard().isSuper()
                                == actualArgument.asWildcard().isSuper()) {
                    ResolvedType expectedBound = expectedArgument.asWildcard().getBoundedType();
                    ResolvedType actualBound = actualArgument.asWildcard().getBoundedType();
                    if (expectedBound.isTypeVariable()
                            && actualBound.isTypeVariable()
                            && expectedBound
                                    .asTypeParameter()
                                    .getQualifiedName()
                                    .equals(actualBound.asTypeParameter().getQualifiedName())) {
                        continue;
                    }
                }
                // Preserve the capture's declared upper bound as well as its wildcard lower bound.
                if (actualArgument.isWildcard() && actualArgument.asWildcard().isSuper()) {
                    actualArgument = captureSuperArgument(actualReference, i);
                }
                matchTypeParameters(expectedArgument, actualArgument, constraints, ConstraintKind.EQUALITY);
            }
        } else if (expectedType.isWildcard()) {
            ResolvedWildcard expectedWildcard = expectedType.asWildcard();
            if (!expectedWildcard.isBounded()) {
                return;
            }
            ConstraintKind boundKind = expectedWildcard.isExtends() ? ConstraintKind.LOWER : ConstraintKind.UPPER;
            if (actualType.isWildcard()) {
                ResolvedWildcard actualWildcard = actualType.asWildcard();
                if ((expectedWildcard.isExtends() && actualWildcard.isExtends())
                        || (expectedWildcard.isSuper() && actualWildcard.isSuper())) {
                    matchTypeParameters(
                            expectedWildcard.getBoundedType(), actualWildcard.getBoundedType(), constraints, boundKind);
                }
            } else if (actualType.isReferenceType() || actualType.isArray() || actualType.isTypeVariable()) {
                matchTypeParameters(expectedWildcard.getBoundedType(), actualType, constraints, boundKind);
            }
        }
    }

    private ResolvedType captureSuperArgument(ResolvedReferenceType reference, int index) {
        ResolvedType argument = reference.typeParametersValues().get(index);
        if (!argument.isWildcard() || !argument.asWildcard().isSuper()) {
            return argument;
        }
        List<ResolvedType> upperBounds = new ArrayList<>();
        ResolvedTypeParameterDeclaration parameter =
                reference.getTypeDeclaration().get().getTypeParameters().get(index);
        for (ResolvedTypeParameterDeclaration.Bound bound : parameter.getBounds()) {
            if (bound.isExtends()) {
                upperBounds.add(reference.typeParametersMap().replaceAll(bound.getType()));
            }
        }
        if (upperBounds.isEmpty()) {
            upperBounds.add(new ReferenceTypeImpl(typeSolver.getSolvedJavaLangObject()));
        }
        return new ResolvedCaptureType(argument.asWildcard(), upperBounds);
    }

    private Optional<MethodUsage> solveMethodAsUsage(
            ResolvedTypeVariable tp, String name, List<ResolvedType> argumentsTypes, Context invokationContext) {
        List<ResolvedTypeParameterDeclaration.Bound> bounds =
                tp.asTypeParameter().getBounds();

        if (bounds.isEmpty()) {
            // if the bounds of a type parameter are empty, then the bound is implicitly "extends Object"
            // we don't make this _ex_plicit in the data representation because that would affect codegen
            // and make everything generate like <T extends Object> instead of <T>
            // https://github.com/javaparser/javaparser/issues/2044
            bounds = Collections.singletonList(ResolvedTypeParameterDeclaration.Bound.extendsBound(
                    new ReferenceTypeImpl(typeSolver.getSolvedJavaLangObject())));
            ;
        }

        for (ResolvedTypeParameterDeclaration.Bound bound : bounds) {
            Optional<MethodUsage> methodUsage =
                    solveMethodAsUsage(bound.getType(), name, argumentsTypes, invokationContext);
            if (methodUsage.isPresent()) {
                return methodUsage;
            }
        }

        return Optional.empty();
    }

    private Optional<MethodUsage> solveMethodAsUsage(
            ResolvedType type, String name, List<ResolvedType> argumentsTypes, Context invokationContext) {
        if (type instanceof ResolvedIntersectionType) {
            for (ResolvedType element : ((ResolvedIntersectionType) type).getElements()) {
                Optional<MethodUsage> usage = solveMethodAsUsage(element, name, argumentsTypes, invokationContext);
                if (usage.isPresent()) {
                    return usage;
                }
            }
            return Optional.empty();
        }
        if (type instanceof ResolvedReferenceType) {
            return solveMethodAsUsage((ResolvedReferenceType) type, name, argumentsTypes, invokationContext);
        }
        if (type instanceof LazyType) {
            return solveMethodAsUsage(type.asReferenceType(), name, argumentsTypes, invokationContext);
        }
        if (type instanceof ResolvedTypeVariable) {
            return solveMethodAsUsage((ResolvedTypeVariable) type, name, argumentsTypes, invokationContext);
        }
        if (type instanceof ResolvedWildcard) {
            ResolvedWildcard wildcardUsage = (ResolvedWildcard) type;
            if (wildcardUsage.isExtends()) {
                return solveMethodAsUsage(wildcardUsage.getBoundedType(), name, argumentsTypes, invokationContext);
            }
            return solveMethodAsUsage(
                    new ReferenceTypeImpl(typeSolver.getSolvedJavaLangObject()),
                    name,
                    argumentsTypes,
                    invokationContext);
        }
        if (type instanceof ResolvedLambdaConstraintType) {
            ResolvedLambdaConstraintType constraintType = (ResolvedLambdaConstraintType) type;
            return solveMethodAsUsage(constraintType.getBound(), name, argumentsTypes, invokationContext);
        }
        if (type instanceof ResolvedArrayType) {
            // An array inherits methods from Object not from it's component type
            return solveMethodAsUsage(
                    new ReferenceTypeImpl(typeSolver.getSolvedJavaLangObject()),
                    name,
                    argumentsTypes,
                    invokationContext);
        }
        if (type instanceof ResolvedUnionType) {
            Optional<ResolvedReferenceType> commonAncestor = type.asUnionType().getCommonAncestor();
            if (commonAncestor.isPresent()) {
                return solveMethodAsUsage(commonAncestor.get(), name, argumentsTypes, invokationContext);
            }
            throw new UnsupportedOperationException("no common ancestor available for " + type.describe());
        }
        throw new UnsupportedOperationException("type usage: " + type.getClass().getCanonicalName());
    }

    private ResolvedType usingParameterTypesFromScope(
            ResolvedType scope, ResolvedType type, Map<ResolvedTypeParameterDeclaration, ResolvedType> inferredTypes) {
        if (type.isReferenceType()) {
            for (Pair<ResolvedTypeParameterDeclaration, ResolvedType> entry :
                    type.asReferenceType().getTypeParametersMap()) {
                if (entry.a.declaredOnType()
                        && scope.isReferenceType()
                        && scope.asReferenceType()
                                .getGenericParameterByName(entry.a.getName())
                                .isPresent()) {
                    type = type.replaceTypeVariables(
                            entry.a,
                            scope.asReferenceType()
                                    .getGenericParameterByName(entry.a.getName())
                                    .get(),
                            inferredTypes);
                }
            }
        }
        return type;
    }

    private ResolvedType applyInferredTypes(
            ResolvedType type, Map<ResolvedTypeParameterDeclaration, ResolvedType> inferredTypes) {
        for (ResolvedTypeParameterDeclaration tp : inferredTypes.keySet()) {
            type = type.replaceTypeVariables(tp, inferredTypes.get(tp), inferredTypes);
        }
        return type;
    }
}
