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

package com.github.javaparser.symbolsolver.javaparsermodel.declarations;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.type.UnknownType;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedParameterDeclaration;
import com.github.javaparser.resolution.model.Value;
import com.github.javaparser.resolution.types.ResolvedArrayType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.LambdaExprContext;

import java.util.Optional;

/**
 * @author Federico Tomassetti
 */
public class JavaParserParameterDeclaration implements ResolvedParameterDeclaration {

    private final Parameter wrappedNode;
    private final TypeSolver typeSolver;

    public JavaParserParameterDeclaration(Parameter wrappedNode, TypeSolver typeSolver) {
        this.wrappedNode = wrappedNode;
        this.typeSolver = typeSolver;
    }

    @Override
    public String getName() {
        return wrappedNode.getName().getId();
    }

    @Override
    public boolean isVariadic() {
        return wrappedNode.isVarArgs();
    }

    @Override
    public ResolvedType getType() {
        if (wrappedNode.getType() instanceof UnknownType && JavaParserFactory.getContext(wrappedNode, typeSolver) instanceof LambdaExprContext) {
            Optional<Value> value = JavaParserFactory.getContext(wrappedNode, typeSolver).solveSymbolAsValue(wrappedNode.getNameAsString());
            if (value.isPresent()) {
                return value.get().getType();
            }
        }
        ResolvedType res = JavaParserFacade.get(typeSolver).convert(wrappedNode.getType(), wrappedNode);
        if (isVariadic()) {
            res = new ResolvedArrayType(res);
        }
        return res;
    }

    /**
     * Returns the JavaParser node associated with this JavaParserParameterDeclaration.
     *
     * @return A visitable JavaParser node wrapped by this object.
     */

    public Parameter getWrappedNode() {
        return wrappedNode;
    }

    @Override
    public Optional<Node> toAst() {
        return Optional.of(wrappedNode);
    }

}
