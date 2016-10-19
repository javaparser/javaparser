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


import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import javaslang.Tuple2;

import com.github.javaparser.symbolsolver.model.declarations.MethodDeclaration;
import com.github.javaparser.symbolsolver.logic.FunctionalInterfaceLogic;
import com.github.javaparser.symbolsolver.logic.GenericTypeInferenceLogic;
import com.github.javaparser.symbolsolver.model.declarations.TypeDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.ValueDeclaration;
import com.github.javaparser.symbolsolver.model.usages.MethodUsage;
import com.github.javaparser.symbolsolver.model.declarations.TypeParameterDeclaration;
import com.github.javaparser.symbolsolver.model.usages.typesystem.Type;
import com.github.javaparser.symbolsolver.resolution.SymbolDeclarator;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.resolution.Value;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static com.github.javaparser.symbolsolver.javaparser.Navigator.getParentNode;

public class LambdaExprContext extends AbstractJavaParserContext<LambdaExpr> {

    public LambdaExprContext(LambdaExpr wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public Optional<Value> solveSymbolAsValue(String name, TypeSolver typeSolver) {
        for (Parameter parameter : wrappedNode.getParameters()) {
            SymbolDeclarator sb = JavaParserFactory.getSymbolDeclarator(parameter, typeSolver);
            int index = 0;
            for (ValueDeclaration decl : sb.getSymbolDeclarations()) {
                if (decl.getName().equals(name)) {
                    if (getParentNode(wrappedNode) instanceof MethodCallExpr) {
                        MethodCallExpr methodCallExpr = (MethodCallExpr) getParentNode(wrappedNode);
                        MethodUsage methodUsage = JavaParserFacade.get(typeSolver).solveMethodAsUsage(methodCallExpr);
                        int i = pos(methodCallExpr, wrappedNode);
                        Type lambdaType = methodUsage.getParamTypes().get(i);
                        Value value = new Value(lambdaType.asReferenceType().typeParametersValues().get(0), name, false);
                        return Optional.of(value);
                    } else if (getParentNode(wrappedNode) instanceof VariableDeclarator) {
                        VariableDeclarator variableDeclarator = (VariableDeclarator) getParentNode(wrappedNode);
                        Type t = JavaParserFacade.get(typeSolver).convertToUsageVariableType(variableDeclarator);
                        Optional<MethodUsage> functionalMethod = FunctionalInterfaceLogic.getFunctionalMethod(t);
                        if (functionalMethod.isPresent()) {
                            Type lambdaType = functionalMethod.get().getParamType(index);

                            // Replace parameter from declarator
                            if (lambdaType.isReferenceType()) {
                                for (Tuple2<TypeParameterDeclaration, Type> entry : lambdaType.asReferenceType().getTypeParametersMap()) {
                                    if (entry._2.isTypeVariable() && entry._2.asTypeParameter().declaredOnClass()) {
                                        Optional<Type> ot = t.asReferenceType().getGenericParameterByName(entry._1.getName());
                                        if (ot.isPresent()) {
                                            lambdaType = lambdaType.replaceParam(entry._1.getName(), ot.get());
                                        }
                                    }
                                }
                            } else if (lambdaType.isTypeVariable() && lambdaType.asTypeParameter().declaredOnClass()) {
                                Optional<Type> ot = t.asReferenceType().getGenericParameterByName(lambdaType.asTypeParameter().getName());
                                if (ot.isPresent()) {
                                    lambdaType = ot.get();
                                }
                            }

                            Value value = new Value(lambdaType, name, false);
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
        return getParent().solveSymbolAsValue(name, typeSolver);
    }

    @Override
    public Optional<Type> solveGenericType(String name, TypeSolver typeSolver) {
        MethodCallExpr parentNode = (MethodCallExpr) getParentNode(wrappedNode);
        int pos = pos(parentNode, wrappedNode);
        MethodUsage methodUsage = JavaParserFacade.get(typeSolver).solveMethodAsUsage((MethodCallExpr) parentNode);
        Type lambda = methodUsage.getParamTypes().get(pos);

        List<Tuple2<Type, Type>> formalActualTypePairs = new ArrayList<>();
        for (int i=0;i<methodUsage.getDeclaration().getNoParams();i++){
            formalActualTypePairs.add(new Tuple2<>(methodUsage.getDeclaration().getParam(i).getType(), methodUsage.getParamType(i)));
        }
        Map<String, Type> map = GenericTypeInferenceLogic.inferGenericTypes(formalActualTypePairs);
        if (map.containsKey(name)) {
            return Optional.of(map.get(name));
        } else {
            return Optional.empty();
        }

        //return Optional.of(lambda.asReferenceType().typeParametersValues().get(0));
    }

    private int pos(MethodCallExpr callExpr, Expression param) {
        int i = 0;
        for (Expression p : callExpr.getArgs()) {
            if (p == param) {
                return i;
            }
            i++;
        }
        throw new IllegalArgumentException();
    }

    protected final Optional<Value> solveWithAsValue(SymbolDeclarator symbolDeclarator, String name, TypeSolver typeSolver) {
        for (ValueDeclaration decl : symbolDeclarator.getSymbolDeclarations()) {
            if (decl.getName().equals(name)) {

                throw new UnsupportedOperationException();
            }
        }
        return Optional.empty();
    }

    @Override
    public SymbolReference<? extends ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        for (Parameter parameter : wrappedNode.getParameters()) {
            SymbolDeclarator sb = JavaParserFactory.getSymbolDeclarator(parameter, typeSolver);
            SymbolReference<ValueDeclaration> symbolReference = solveWith(sb, name);
            if (symbolReference.isSolved()) {
                return symbolReference;
            }
        }

        // if nothing is found we should ask the parent context
        return getParent().solveSymbol(name, typeSolver);
    }

    @Override
    public SymbolReference<TypeDeclaration> solveType(String name, TypeSolver typeSolver) {
        return getParent().solveType(name, typeSolver);
    }

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(
            String name, List<Type> argumentsTypes, TypeSolver typeSolver) {
        return getParent().solveMethod(name, argumentsTypes, typeSolver);
    }

}
