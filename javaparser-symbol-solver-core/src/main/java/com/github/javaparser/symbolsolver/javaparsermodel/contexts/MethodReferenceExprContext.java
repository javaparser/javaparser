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

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.MethodReferenceExpr;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.logic.ConstructorResolutionLogic;
import com.github.javaparser.resolution.logic.FunctionalInterfaceLogic;
import com.github.javaparser.resolution.logic.InferenceContext;
import com.github.javaparser.resolution.logic.MethodResolutionLogic;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedLambdaConstraintType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import java.util.*;

public class MethodReferenceExprContext extends ExpressionContext<MethodReferenceExpr> {

    ///
    /// Constructors
    ///

    public MethodReferenceExprContext(MethodReferenceExpr wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    ///
    /// Public methods
    ///

    @Override
    public SymbolReference<ResolvedMethodDeclaration> solveMethod(
            String name, List<ResolvedType> argumentsTypes, boolean staticOnly) {
        // A constructor reference does not denote a method; it is resolved by solveConstructor().
        if (MethodReferenceExpr.CONSTRUCTOR_REFERENCE_IDENTIFIER.equals(name)) {
            return SymbolReference.unsolved();
        }

        argumentsTypes.addAll(inferArgumentTypes());

        Collection<ResolvedReferenceTypeDeclaration> rrtds = findTypeDeclarations(Optional.of(wrappedNode.getScope()));

        if (rrtds.isEmpty()) {
            // if the bounds of a type parameter are empty, then the bound is implicitly "extends Object"
            // we don't make this _ex_plicit in the data representation because that would affect codegen
            // and make everything generate like <T extends Object> instead of <T>
            // https://github.com/javaparser/javaparser/issues/2044
            rrtds = Collections.singleton(typeSolver.getSolvedJavaLangObject());
        }

        for (ResolvedReferenceTypeDeclaration rrtd : rrtds) {
            SymbolReference<ResolvedMethodDeclaration> firstResAttempt =
                    MethodResolutionLogic.solveMethodInType(rrtd, name, argumentsTypes, false);
            if (firstResAttempt.isSolved()) {
                return firstResAttempt;
            }
            SymbolReference<ResolvedMethodDeclaration> secondResAttempt =
                    MethodResolutionLogic.solveMethodInType(rrtd, name, Collections.emptyList(), false);
            if (secondResAttempt.isSolved()) {
                return secondResAttempt;
            }
        }

        return SymbolReference.unsolved();
    }

    /**
     * Given a constructor reference (e.g. {@code Foo::new}) find out to which constructor declaration it
     * corresponds. The candidate constructors are those of the scope type, and they are matched against the
     * parameter types of the functional interface method the reference is assigned to, so that
     * {@code Supplier<Foo>} selects {@code Foo()} while {@code Function<String, Foo>} selects
     * {@code Foo(String)}.
     *
     * @param argumentsTypes an empty, mutable list which is populated with the inferred argument types.
     * @return the referenced constructor, or an unsolved reference when this is not a constructor reference,
     *         when it is an array constructor reference, or when no constructor is applicable.
     */
    public SymbolReference<ResolvedConstructorDeclaration> solveConstructor(List<ResolvedType> argumentsTypes) {
        if (!wrappedNode.isConstructorReference()) {
            return SymbolReference.unsolved();
        }
        // JLS 15.13.1: an array constructor reference such as String[]::new denotes array creation, for
        // which no constructor declaration exists. It has to be rejected here because
        // findTypeDeclarations() maps an array scope to java.lang.Object, which would otherwise make
        // String[]::new resolve to a constructor of Object.
        if (isArrayConstructorReference()) {
            return SymbolReference.unsolved();
        }

        argumentsTypes.addAll(inferArgumentTypes());

        // Unlike MethodResolutionLogic, ConstructorResolutionLogic does not know about the lambda
        // constraint types that inferArgumentTypes() produces, so they are replaced by their bound.
        List<ResolvedType> boundArgumentsTypes = new ArrayList<>(argumentsTypes.size());
        for (ResolvedType argumentType : argumentsTypes) {
            boundArgumentsTypes.add(
                    argumentType.isConstraint()
                            ? argumentType.asConstraintType().getBound()
                            : argumentType);
        }

        for (ResolvedReferenceTypeDeclaration rrtd : findTypeDeclarations(Optional.of(wrappedNode.getScope()))) {
            SymbolReference<ResolvedConstructorDeclaration> resAttempt = ConstructorResolutionLogic.findMostApplicable(
                    rrtd.getConstructors(), boundArgumentsTypes, typeSolver);
            if (resAttempt.isSolved()) {
                return resAttempt;
            }
        }

        return SymbolReference.unsolved();
    }

    ///
    /// Private methods
    ///

    private boolean isArrayConstructorReference() {
        Expression scope = wrappedNode.getScope();
        return scope.isTypeExpr() && scope.asTypeExpr().getType().isArrayType();
    }

    private List<ResolvedType> inferArgumentTypes() {
        if (demandParentNode(wrappedNode) instanceof MethodCallExpr) {
            MethodCallExpr methodCallExpr = (MethodCallExpr) demandParentNode(wrappedNode);
            MethodUsage methodUsage = JavaParserFacade.get(typeSolver).solveMethodAsUsage(methodCallExpr);
            int pos = methodCallExpr.getArgumentPosition(wrappedNode);
            ResolvedMethodDeclaration rmd = methodUsage.getDeclaration();
            // Since variable parameters are represented by an array, in case we deal with
            // the variadic parameter we have to take into account the base type of the
            // array.
            ResolvedType lambdaType = (rmd.hasVariadicParameter() && pos >= rmd.getNumberOfParams() - 1)
                    ? rmd.getLastParam().getType().asArrayType().getComponentType()
                    : methodUsage.getParamType(pos);

            return resolveLambdaTypes(lambdaType);
        }

        if (demandParentNode(wrappedNode) instanceof ObjectCreationExpr) {
            ObjectCreationExpr objectCreationExpr = (ObjectCreationExpr) demandParentNode(wrappedNode);
            ResolvedConstructorDeclaration rcd =
                    JavaParserFacade.get(typeSolver).solve(objectCreationExpr).getCorrespondingDeclaration();
            int pos = objectCreationExpr.getArgumentPosition(wrappedNode);
            // Since variable parameters are represented by an array, in case we deal with
            // the variadic parameter we have to take into account the base type of the
            // array.
            ResolvedType lambdaType = (rcd.hasVariadicParameter() && pos >= rcd.getNumberOfParams() - 1)
                    ? rcd.getLastParam().getType().asArrayType().getComponentType()
                    : rcd.getParam(pos).getType();

            return resolveLambdaTypes(lambdaType);
        }

        if (demandParentNode(wrappedNode) instanceof VariableDeclarator) {
            VariableDeclarator variableDeclarator = (VariableDeclarator) demandParentNode(wrappedNode);
            ResolvedType t = JavaParserFacade.get(typeSolver).convertToUsage(variableDeclarator.getType());
            Optional<MethodUsage> functionalMethod = FunctionalInterfaceLogic.getFunctionalMethod(t);
            if (functionalMethod.isPresent()) {
                List<ResolvedType> resolvedTypes = new ArrayList<>();
                for (ResolvedType lambdaType : functionalMethod.get().getParamTypes()) {
                    // Replace parameter from declarator
                    Map<ResolvedTypeParameterDeclaration, ResolvedType> inferredTypes = new HashMap<>();
                    if (lambdaType.isReferenceType()) {
                        for (com.github.javaparser.utils.Pair<ResolvedTypeParameterDeclaration, ResolvedType> entry :
                                lambdaType.asReferenceType().getTypeParametersMap()) {
                            if (entry.b.isTypeVariable()
                                    && entry.b.asTypeParameter().declaredOnType()) {
                                ResolvedType ot =
                                        t.asReferenceType().typeParametersMap().getValue(entry.a);
                                lambdaType = lambdaType.replaceTypeVariables(entry.a, ot, inferredTypes);
                            }
                        }
                    } else if (lambdaType.isTypeVariable()
                            && lambdaType.asTypeParameter().declaredOnType()) {
                        lambdaType = t.asReferenceType().typeParametersMap().getValue(lambdaType.asTypeParameter());
                    }
                    resolvedTypes.add(lambdaType);
                }

                return resolvedTypes;
            }
            throw new UnsupportedOperationException();
        }

        if (demandParentNode(wrappedNode) instanceof ReturnStmt) {
            ReturnStmt returnStmt = (ReturnStmt) demandParentNode(wrappedNode);
            Optional<MethodDeclaration> optDeclaration = returnStmt.findAncestor(MethodDeclaration.class);
            if (optDeclaration.isPresent()) {
                ResolvedType t = JavaParserFacade.get(typeSolver)
                        .convertToUsage(
                                optDeclaration.get().asMethodDeclaration().getType());
                Optional<MethodUsage> functionalMethod = FunctionalInterfaceLogic.getFunctionalMethod(t);
                if (functionalMethod.isPresent()) {
                    List<ResolvedType> resolvedTypes = new ArrayList<>();
                    for (ResolvedType lambdaType : functionalMethod.get().getParamTypes()) {
                        // Replace parameter from declarator
                        Map<ResolvedTypeParameterDeclaration, ResolvedType> inferredTypes = new HashMap<>();
                        if (lambdaType.isReferenceType()) {
                            for (com.github.javaparser.utils.Pair<ResolvedTypeParameterDeclaration, ResolvedType>
                                    entry : lambdaType.asReferenceType().getTypeParametersMap()) {
                                if (entry.b.isTypeVariable()
                                        && entry.b.asTypeParameter().declaredOnType()) {
                                    ResolvedType ot = t.asReferenceType()
                                            .typeParametersMap()
                                            .getValue(entry.a);
                                    lambdaType = lambdaType.replaceTypeVariables(entry.a, ot, inferredTypes);
                                }
                            }
                        } else if (lambdaType.isTypeVariable()
                                && lambdaType.asTypeParameter().declaredOnType()) {
                            lambdaType = t.asReferenceType().typeParametersMap().getValue(lambdaType.asTypeParameter());
                        }
                        resolvedTypes.add(lambdaType);
                    }

                    return resolvedTypes;
                }
                throw new UnsupportedOperationException();
            }
            throw new UnsupportedOperationException();
        }
        throw new UnsupportedOperationException();
    }

    private List<ResolvedType> resolveLambdaTypes(ResolvedType lambdaType) {
        // Get the functional method in order for us to resolve it's type arguments properly
        Optional<MethodUsage> functionalMethodOpt = FunctionalInterfaceLogic.getFunctionalMethod(lambdaType);
        if (functionalMethodOpt.isPresent()) {
            MethodUsage functionalMethod = functionalMethodOpt.get();

            List<ResolvedType> resolvedTypes = new ArrayList<>();

            for (ResolvedType type : functionalMethod.getParamTypes()) {
                InferenceContext inferenceContext = new InferenceContext(typeSolver);

                // Resolve each type variable of the lambda, and use this later to infer the type of each
                // implicit parameter
                inferenceContext.addPair(new ReferenceTypeImpl(functionalMethod.declaringType()), lambdaType);

                // Now resolve the argument type using the inference context
                ResolvedType argType = inferenceContext.resolve(inferenceContext.addSingle(type));

                ResolvedLambdaConstraintType conType;
                if (argType.isWildcard()) {
                    conType = ResolvedLambdaConstraintType.bound(
                            argType.asWildcard().getBoundedType());
                } else {
                    conType = ResolvedLambdaConstraintType.bound(argType);
                }

                resolvedTypes.add(conType);
            }

            return resolvedTypes;
        }
        throw new UnsupportedOperationException();
    }
}
