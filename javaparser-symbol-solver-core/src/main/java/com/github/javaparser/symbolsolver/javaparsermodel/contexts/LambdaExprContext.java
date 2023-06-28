/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2023 The JavaParser Team.
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

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.CastExpr;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.SymbolDeclarator;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.logic.FunctionalInterfaceLogic;
import com.github.javaparser.resolution.logic.InferenceContext;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.model.Value;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedLambdaConstraintType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;

import java.util.*;

import static com.github.javaparser.ast.expr.Expression.EXCLUDE_ENCLOSED_EXPR;
import static com.github.javaparser.ast.expr.Expression.IS_NOT_ENCLOSED_EXPR;
import static com.github.javaparser.resolution.Navigator.demandParentNode;

/**
 * @author Federico Tomassetti
 */
public class LambdaExprContext extends AbstractJavaParserContext<LambdaExpr> {
    
    public LambdaExprContext(LambdaExpr wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public Optional<Value> solveSymbolAsValue(String name) {
        int index = -1;
        for (Parameter parameter : wrappedNode.getParameters()) {
            index++;
            SymbolDeclarator sb = JavaParserFactory.getSymbolDeclarator(parameter, typeSolver);
            for (ResolvedValueDeclaration decl : sb.getSymbolDeclarations()) {
                if (decl.getName().equals(name)) {
                    Node parentNode = demandParentNode(wrappedNode, IS_NOT_ENCLOSED_EXPR);
                    if (parentNode instanceof MethodCallExpr) {
                        MethodCallExpr methodCallExpr = (MethodCallExpr) parentNode;
                        MethodUsage methodUsage = JavaParserFacade.get(typeSolver).solveMethodAsUsage(methodCallExpr);
                        int i = methodCallExpr.getArgumentPosition(wrappedNode, EXCLUDE_ENCLOSED_EXPR);
                        ResolvedType lambdaType = methodUsage.getParamTypes().get(i);

                        // Get the functional method in order for us to resolve it's type arguments properly
                        Optional<MethodUsage> functionalMethodOpt = FunctionalInterfaceLogic.getFunctionalMethod(lambdaType);
                        if (functionalMethodOpt.isPresent()) {
                            MethodUsage functionalMethod = functionalMethodOpt.get();
                            InferenceContext inferenceContext = new InferenceContext(typeSolver);

                            // Resolve each type variable of the lambda, and use this later to infer the type of each
                            // implicit parameter
                            lambdaType.asReferenceType().getTypeDeclaration().ifPresent(typeDeclaration -> {
                                inferenceContext.addPair(
                                        lambdaType,
                                        new ReferenceTypeImpl(typeDeclaration)
                                );
                            });

                            // Find the position of this lambda argument
                            boolean found = false;
                            int lambdaParamIndex;
                            for (lambdaParamIndex = 0; lambdaParamIndex < wrappedNode.getParameters().size(); lambdaParamIndex++){
                                if (wrappedNode.getParameter(lambdaParamIndex).getName().getIdentifier().equals(name)){
                                    found = true;
                                    break;
                                }
                            }
                            if (!found) { return Optional.empty(); }

                            // Now resolve the argument type using the inference context
                            ResolvedType argType = inferenceContext.resolve(inferenceContext.addSingle(functionalMethod.getParamType(lambdaParamIndex)));

                            ResolvedLambdaConstraintType conType;
                            if (argType.isWildcard()){
                                conType = ResolvedLambdaConstraintType.bound(argType.asWildcard().getBoundedType());
                            } else {
                                conType = ResolvedLambdaConstraintType.bound(argType);
                            }
                            Value value = new Value(conType, name);
                            return Optional.of(value);
                        }
                        return Optional.empty();
                    }
                                    if (parentNode instanceof VariableDeclarator) {
                        VariableDeclarator variableDeclarator = (VariableDeclarator) parentNode;
                        ResolvedType t = JavaParserFacade.get(typeSolver).convertToUsage(variableDeclarator.getType());
                        Optional<MethodUsage> functionalMethod = FunctionalInterfaceLogic.getFunctionalMethod(t);
                        if (functionalMethod.isPresent()) {
                            ResolvedType lambdaType = functionalMethod.get().getParamType(index);

                            // Replace parameter from declarator
                            Map<ResolvedTypeParameterDeclaration, ResolvedType> inferredTypes = new HashMap<>();
                            if (lambdaType.isReferenceType()) {
                                for (com.github.javaparser.utils.Pair<ResolvedTypeParameterDeclaration, ResolvedType> entry : lambdaType.asReferenceType().getTypeParametersMap()) {
                                    if (entry.b.isTypeVariable() && entry.b.asTypeParameter().declaredOnType()) {
                                        ResolvedType ot = t.asReferenceType().typeParametersMap().getValue(entry.a);
                                        lambdaType = lambdaType.replaceTypeVariables(entry.a, ot, inferredTypes);
                                    }
                                }
                            } else if (lambdaType.isTypeVariable() && lambdaType.asTypeParameter().declaredOnType()) {
                                lambdaType = t.asReferenceType().typeParametersMap().getValue(lambdaType.asTypeParameter());
                            }

                            Value value = new Value(lambdaType, name);
                            return Optional.of(value);
                        }
                        throw new UnsupportedOperationException();
                    }
                    if (parentNode instanceof ReturnStmt) {
                        ReturnStmt returnStmt = (ReturnStmt) parentNode;
                        Optional<MethodDeclaration> optDeclaration = returnStmt.findAncestor(MethodDeclaration.class);
                        if (optDeclaration.isPresent()) {
                            ResolvedType t = JavaParserFacade.get(typeSolver).convertToUsage(optDeclaration.get().asMethodDeclaration().getType());
                            Optional<MethodUsage> functionalMethod = FunctionalInterfaceLogic.getFunctionalMethod(t);

                            if (functionalMethod.isPresent()) {
                                ResolvedType lambdaType = functionalMethod.get().getParamType(index);

                                // Replace parameter from declarator
                                Map<ResolvedTypeParameterDeclaration, ResolvedType> inferredTypes = new HashMap<>();
                                if (lambdaType.isReferenceType()) {
                                    for (com.github.javaparser.utils.Pair<ResolvedTypeParameterDeclaration, ResolvedType> entry : lambdaType.asReferenceType().getTypeParametersMap()) {
                                        if (entry.b.isTypeVariable() && entry.b.asTypeParameter().declaredOnType()) {
                                            ResolvedType ot = t.asReferenceType().typeParametersMap().getValue(entry.a);
                                            lambdaType = lambdaType.replaceTypeVariables(entry.a, ot, inferredTypes);
                                        }
                                    }
                                } else if (lambdaType.isTypeVariable() && lambdaType.asTypeParameter().declaredOnType()) {
                                    lambdaType = t.asReferenceType().typeParametersMap().getValue(lambdaType.asTypeParameter());
                                }

                                Value value = new Value(lambdaType, name);
                                return Optional.of(value);
                            }
                            throw new UnsupportedOperationException();
                        }
                    }
                    if (parentNode instanceof CastExpr) {
                        CastExpr castExpr = (CastExpr) parentNode;
                        ResolvedType t = JavaParserFacade.get(typeSolver).convertToUsage(castExpr.getType());
                        Optional<MethodUsage> functionalMethod = FunctionalInterfaceLogic.getFunctionalMethod(t);

                        if (functionalMethod.isPresent()) {
                            ResolvedType lambdaType = functionalMethod.get().getParamType(index);

                            // Replace parameter from declarator
                            Map<ResolvedTypeParameterDeclaration, ResolvedType> inferredTypes = new HashMap<>();
                            if (lambdaType.isReferenceType()) {
                                for (com.github.javaparser.utils.Pair<ResolvedTypeParameterDeclaration, ResolvedType> entry : lambdaType.asReferenceType().getTypeParametersMap()) {
                                    if (entry.b.isTypeVariable() && entry.b.asTypeParameter().declaredOnType()) {
                                        ResolvedType ot = t.asReferenceType().typeParametersMap().getValue(entry.a);
                                        lambdaType = lambdaType.replaceTypeVariables(entry.a, ot, inferredTypes);
                                    }
                                }
                            } else if (lambdaType.isTypeVariable() && lambdaType.asTypeParameter().declaredOnType()) {
                                lambdaType = t.asReferenceType().typeParametersMap().getValue(lambdaType.asTypeParameter());
                            }

                            Value value = new Value(lambdaType, name);
                            return Optional.of(value);
                        }
                        throw new UnsupportedOperationException();
                    }
                    throw new UnsupportedOperationException();
                }
            }
        }

        // if nothing is found we should ask the parent context
        return solveSymbolAsValueInParentContext(name);
    }

    @Override
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name) {
        for (Parameter parameter : wrappedNode.getParameters()) {
            SymbolDeclarator sb = JavaParserFactory.getSymbolDeclarator(parameter, typeSolver);
            SymbolReference<ResolvedValueDeclaration> symbolReference = solveWith(sb, name);
            if (symbolReference.isSolved()) {
                return symbolReference;
            }
        }

        // if nothing is found we should ask the parent context
        return solveSymbolInParentContext(name);
    }

    @Override
    public SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> argumentsTypes, boolean staticOnly) {
        // TODO: Document why staticOnly is forced to be false.
        return solveMethodInParentContext(name, argumentsTypes, false);
    }

    @Override
    public List<Parameter> parametersExposedToChild(Node child) {
        // TODO/FIXME: Presumably the parameters must be exposed to all children and their descendants, not just the direct child?
        if (child == wrappedNode.getBody()) {
            return wrappedNode.getParameters();
        }
        return Collections.emptyList();
    }

    ///
    /// Protected methods
    ///

    protected final Optional<Value> solveWithAsValue(SymbolDeclarator symbolDeclarator, String name) {
        for (ResolvedValueDeclaration decl : symbolDeclarator.getSymbolDeclarations()) {
            if (decl.getName().equals(name)) {

                throw new UnsupportedOperationException();
            }
        }
        return Optional.empty();
    }
}
