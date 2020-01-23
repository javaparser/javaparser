/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2020 The JavaParser Team.
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

package org.javaparser.symbolsolver.javaparsermodel.contexts;

import org.javaparser.ast.Node;
import org.javaparser.ast.body.MethodDeclaration;
import org.javaparser.ast.body.Parameter;
import org.javaparser.ast.body.VariableDeclarator;
import org.javaparser.ast.expr.Expression;
import org.javaparser.ast.expr.LambdaExpr;
import org.javaparser.ast.expr.MethodCallExpr;
import org.javaparser.ast.stmt.ReturnStmt;
import org.javaparser.resolution.MethodUsage;
import org.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import org.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import org.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import org.javaparser.resolution.declarations.ResolvedValueDeclaration;
import org.javaparser.resolution.types.ResolvedLambdaConstraintType;
import org.javaparser.resolution.types.ResolvedType;
import org.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import org.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import org.javaparser.symbolsolver.logic.FunctionalInterfaceLogic;
import org.javaparser.symbolsolver.logic.InferenceContext;
import org.javaparser.symbolsolver.model.resolution.SymbolReference;
import org.javaparser.symbolsolver.model.resolution.TypeSolver;
import org.javaparser.symbolsolver.model.resolution.Value;
import org.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import org.javaparser.symbolsolver.reflectionmodel.MyObjectProvider;
import org.javaparser.symbolsolver.resolution.SymbolDeclarator;

import java.util.*;

import static org.javaparser.symbolsolver.javaparser.Navigator.demandParentNode;

/**
 * @author Federico Tomassetti
 */
public class LambdaExprContext extends AbstractJavaParserContext<LambdaExpr> {

    public LambdaExprContext(LambdaExpr wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public Optional<Value> solveSymbolAsValue(String name) {
        for (Parameter parameter : wrappedNode.getParameters()) {
            SymbolDeclarator sb = JavaParserFactory.getSymbolDeclarator(parameter, typeSolver);
            int index = 0;
            for (ResolvedValueDeclaration decl : sb.getSymbolDeclarations()) {
                if (decl.getName().equals(name)) {
                    if (demandParentNode(wrappedNode) instanceof MethodCallExpr) {
                        MethodCallExpr methodCallExpr = (MethodCallExpr) demandParentNode(wrappedNode);
                        MethodUsage methodUsage = JavaParserFacade.get(typeSolver).solveMethodAsUsage(methodCallExpr);
                        int i = pos(methodCallExpr, wrappedNode);
                        ResolvedType lambdaType = methodUsage.getParamTypes().get(i);

                        // Get the functional method in order for us to resolve it's type arguments properly
                        Optional<MethodUsage> functionalMethodOpt = FunctionalInterfaceLogic.getFunctionalMethod(lambdaType);
                        if (functionalMethodOpt.isPresent()){
                            MethodUsage functionalMethod = functionalMethodOpt.get();
                            InferenceContext inferenceContext = new InferenceContext(MyObjectProvider.INSTANCE);

                            // Resolve each type variable of the lambda, and use this later to infer the type of each
                            // implicit parameter
                            inferenceContext.addPair(lambdaType, new ReferenceTypeImpl(lambdaType.asReferenceType().getTypeDeclaration(), typeSolver));

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
                        } else{
                            return Optional.empty();
                        }
                    } else if (demandParentNode(wrappedNode) instanceof VariableDeclarator) {
                        VariableDeclarator variableDeclarator = (VariableDeclarator) demandParentNode(wrappedNode);
                        ResolvedType t = JavaParserFacade.get(typeSolver).convertToUsageVariableType(variableDeclarator);
                        Optional<MethodUsage> functionalMethod = FunctionalInterfaceLogic.getFunctionalMethod(t);
                        if (functionalMethod.isPresent()) {
                            ResolvedType lambdaType = functionalMethod.get().getParamType(index);

                            // Replace parameter from declarator
                            Map<ResolvedTypeParameterDeclaration, ResolvedType> inferredTypes = new HashMap<>();
                            if (lambdaType.isReferenceType()) {
                                for (org.javaparser.utils.Pair<ResolvedTypeParameterDeclaration, ResolvedType> entry : lambdaType.asReferenceType().getTypeParametersMap()) {
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
                        } else {
                            throw new UnsupportedOperationException();
                        }
                    } else if (demandParentNode(wrappedNode) instanceof ReturnStmt) {
                        ReturnStmt returnStmt = (ReturnStmt) demandParentNode(wrappedNode);
                        Optional<MethodDeclaration> optDeclaration = returnStmt.findAncestor(MethodDeclaration.class);
                        if (optDeclaration.isPresent()) {
                            ResolvedType t = JavaParserFacade.get(typeSolver).convertToUsage(optDeclaration.get().asMethodDeclaration().getType());
                            Optional<MethodUsage> functionalMethod = FunctionalInterfaceLogic.getFunctionalMethod(t);

                            if (functionalMethod.isPresent()) {
                                ResolvedType lambdaType = functionalMethod.get().getParamType(index);

                                // Replace parameter from declarator
                                Map<ResolvedTypeParameterDeclaration, ResolvedType> inferredTypes = new HashMap<>();
                                if (lambdaType.isReferenceType()) {
                                    for (org.javaparser.utils.Pair<ResolvedTypeParameterDeclaration, ResolvedType> entry : lambdaType.asReferenceType().getTypeParametersMap()) {
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
                            } else {
                                throw new UnsupportedOperationException();
                            }
                        }
                    } else {
                        throw new UnsupportedOperationException();
                    }
                }
                index++;
            }
        }

        // if nothing is found we should ask the parent context
        return getParent().solveSymbolAsValue(name);
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
        return getParent().solveSymbol(name);
    }

    @Override
    public SymbolReference<ResolvedTypeDeclaration> solveType(String name) {
        return getParent().solveType(name);
    }

    @Override
    public SymbolReference<ResolvedMethodDeclaration> solveMethod(
            String name, List<ResolvedType> argumentsTypes, boolean staticOnly) {
        return getParent().solveMethod(name, argumentsTypes, false);
    }

    @Override
    public List<Parameter> parametersExposedToChild(Node child) {
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

    ///
    /// Private methods
    ///

    private int pos(MethodCallExpr callExpr, Expression param) {
        int i = 0;
        for (Expression p : callExpr.getArguments()) {
            if (p == param) {
                return i;
            }
            i++;
        }
        throw new IllegalArgumentException();
    }
}
