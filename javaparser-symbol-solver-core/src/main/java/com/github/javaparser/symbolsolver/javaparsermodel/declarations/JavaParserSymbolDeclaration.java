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

package com.github.javaparser.symbolsolver.javaparsermodel.declarations;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.types.ResolvedArrayType;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

import static com.github.javaparser.symbolsolver.javaparser.Navigator.demandParentNode;

/**
 * This should not be used to represent fields of parameters.
 *
 * Eventually this should be renamed in JavaParserVariableDeclaration.
 *
 * @author Federico Tomassetti
 */
public class JavaParserSymbolDeclaration implements ResolvedValueDeclaration {

    private String name;
    private Node wrappedNode;
    private TypeSolver typeSolver;

    private JavaParserSymbolDeclaration(Node wrappedNode, String name, TypeSolver typeSolver) {
        this.name = name;
        this.wrappedNode = wrappedNode;
        this.typeSolver = typeSolver;
    }

    public static JavaParserFieldDeclaration field(VariableDeclarator wrappedNode, TypeSolver typeSolver) {
        return new JavaParserFieldDeclaration(wrappedNode, typeSolver);
    }

    public static JavaParserParameterDeclaration parameter(Parameter parameter, TypeSolver typeSolver) {
        return new JavaParserParameterDeclaration(parameter, typeSolver);
    }

    public static JavaParserSymbolDeclaration localVar(VariableDeclarator variableDeclarator, TypeSolver typeSolver) {
        return new JavaParserSymbolDeclaration(variableDeclarator, variableDeclarator.getName().getId(), typeSolver);
    }

    public static int getParamPos(Parameter parameter) {
        int pos = 0;
        for (Node node : demandParentNode(parameter).getChildNodes()) {
            if (node == parameter) {
                return pos;
            } else if (node instanceof Parameter) {
                pos++;
            }
        }
        return pos;
    }

    public static int getParamPos(Node node) {
        if (demandParentNode(node) instanceof MethodCallExpr) {
            MethodCallExpr call = (MethodCallExpr) demandParentNode(node);
            for (int i = 0; i < call.getArguments().size(); i++) {
                if (call.getArguments().get(i) == node) return i;
            }
            throw new IllegalStateException();
        }
        throw new IllegalArgumentException();
    }

    @Override
    public String toString() {
        return "JavaParserSymbolDeclaration{" +
                "name='" + name + '\'' +
                ", wrappedNode=" + wrappedNode +
                '}';
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public boolean isField() {
        return false;
    }

    @Override
    public boolean isParameter() {
        return false;
    }

    @Override
    public boolean isType() {
        return false;
    }

    @Override
    public ResolvedType getType() {
        if (wrappedNode instanceof Parameter) {
            Parameter parameter = (Parameter) wrappedNode;
            if (demandParentNode(wrappedNode) instanceof LambdaExpr) {
                int pos = getParamPos(parameter);
                ResolvedType lambdaType = JavaParserFacade.get(typeSolver).getType(demandParentNode(wrappedNode));

                // TODO understand from the context to which method this corresponds
                //MethodDeclaration methodDeclaration = JavaParserFacade.get(typeSolver).getMethodCalled
                //MethodDeclaration methodCalled = JavaParserFacade.get(typeSolver).solve()
                throw new UnsupportedOperationException(wrappedNode.getClass().getCanonicalName());
            } else {
                final ResolvedType rawType;
                if (parameter.getType() instanceof com.github.javaparser.ast.type.PrimitiveType) {
                    rawType = ResolvedPrimitiveType.byName(((com.github.javaparser.ast.type.PrimitiveType) parameter.getType()).getType().name());
                } else {
                    rawType = JavaParserFacade.get(typeSolver).convertToUsage(parameter.getType(), wrappedNode);
                }
                if (parameter.isVarArgs()) {
                    return new ResolvedArrayType(rawType);
                }
                return rawType;
            }
        } else if (wrappedNode instanceof VariableDeclarator) {
            VariableDeclarator variableDeclarator = (VariableDeclarator) wrappedNode;
            if (demandParentNode(wrappedNode) instanceof VariableDeclarationExpr) {
                return JavaParserFacade.get(typeSolver).convert(variableDeclarator.getType(), JavaParserFactory.getContext(wrappedNode, typeSolver));
            } else if (demandParentNode(wrappedNode) instanceof FieldDeclaration) {
                return JavaParserFacade.get(typeSolver).convert(variableDeclarator.getType(), JavaParserFactory.getContext(wrappedNode, typeSolver));
            }
        }
        throw new UnsupportedOperationException(wrappedNode.getClass().getCanonicalName());
    }

    @Override
    public ResolvedTypeDeclaration asType() {
        throw new UnsupportedOperationException(this.getClass().getCanonicalName() + ": wrapping " + this.getWrappedNode().getClass().getCanonicalName());
    }

    /**
     * Returns the JavaParser node associated with this JavaParserSymbolDeclaration.
     *
     * @return A visitable JavaParser node wrapped by this object.
     */
    public Node getWrappedNode() {
        return wrappedNode;
    }


}
