/*
 * Copyright 2016 Federico Tomassetti
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.types.ResolvedLambdaConstraintType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.logic.FunctionalInterfaceLogic;
import com.github.javaparser.symbolsolver.logic.InferenceContext;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.resolution.Value;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.reflectionmodel.MyObjectProvider;
import com.github.javaparser.symbolsolver.resolution.SymbolDeclarator;

import java.util.*;

import static com.github.javaparser.symbolsolver.javaparser.Navigator.requireParentNode;

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
                    if (requireParentNode(wrappedNode) instanceof MethodCallExpr) {
                        MethodCallExpr methodCallExpr = (MethodCallExpr) requireParentNode(wrappedNode);
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
                    } else if (requireParentNode(wrappedNode) instanceof VariableDeclarator) {
                        VariableDeclarator variableDeclarator = (VariableDeclarator) requireParentNode(wrappedNode);
                        ResolvedType t = JavaParserFacade.get(typeSolver).convertToUsageVariableType(variableDeclarator);
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
                        } else {
                            throw new UnsupportedOperationException();
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
