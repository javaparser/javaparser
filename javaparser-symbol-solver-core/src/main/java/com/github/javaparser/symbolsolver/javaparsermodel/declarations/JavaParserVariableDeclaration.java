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

import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.resolution.declarations.AssociableToAST;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

import java.util.Optional;

import static com.github.javaparser.symbolsolver.javaparser.Navigator.demandParentNode;

/**
 * @author Federico Tomassetti
 */
public class JavaParserVariableDeclaration implements ResolvedValueDeclaration, AssociableToAST<VariableDeclarationExpr> {

    private VariableDeclarator variableDeclarator;
    private VariableDeclarationExpr wrappedNode;
    private TypeSolver typeSolver;

    public JavaParserVariableDeclaration(VariableDeclarator variableDeclarator, TypeSolver typeSolver) {
        if (typeSolver == null) {
            throw new IllegalArgumentException("typeSolver should not be null");
        }
        this.variableDeclarator = variableDeclarator;
        this.typeSolver = typeSolver;
        if (!(demandParentNode(variableDeclarator) instanceof VariableDeclarationExpr)) {
            throw new IllegalStateException(demandParentNode(variableDeclarator).getClass().getCanonicalName());
        }
        this.wrappedNode = (VariableDeclarationExpr) demandParentNode(variableDeclarator);
    }

    @Override
    public ResolvedType getType() {
        return JavaParserFacade.get(typeSolver).convert(variableDeclarator.getType(), wrappedNode);
    }

    @Override
    public String getName() {
        return variableDeclarator.getName().getId();
    }

    @Override
    public boolean isVariable() {
        return true;
    }

    /**
     * Returns the JavaParser node associated with this JavaParserFieldDeclaration.
     *
     * @return A visitable JavaParser node wrapped by this object.
     */
    public VariableDeclarationExpr getWrappedNode() {
        return wrappedNode;
    }

    public VariableDeclarator getVariableDeclarator() {
        return variableDeclarator;
    }

    @Override
    public String toString() {
        return "JavaParserVariableDeclaration{" + getName() + "}";
    }

    @Override
    public Optional<VariableDeclarationExpr> toAst() {
        return Optional.of(wrappedNode);
    }
}
