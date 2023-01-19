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
import com.github.javaparser.ast.expr.PatternExpr;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedPatternDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;

import java.util.Optional;

/**
 * WARNING: Implemented fairly blindly. Unsure if required or even appropriate. Use with extreme caution.
 *
 * @author Roger Howell
 */
public class JavaParserPatternDeclaration implements ResolvedPatternDeclaration {

    private final PatternExpr wrappedNode;
    private final TypeSolver typeSolver;

    public JavaParserPatternDeclaration(PatternExpr wrappedNode, TypeSolver typeSolver) {
        this.wrappedNode = wrappedNode;
        this.typeSolver = typeSolver;
    }

    @Override
    public String getName() {
        return wrappedNode.getName().getId();
    }

    @Override
    public ResolvedType getType() {
        return JavaParserFacade.get(typeSolver).convert(wrappedNode.getType(), wrappedNode);
    }

    /**
     * Returns the JavaParser node associated with this JavaParserPatternDeclaration.
     *
     * @return A visitable JavaParser node wrapped by this object.
     */
    public PatternExpr getWrappedNode() {
        return wrappedNode;
    }

    @Override
    public Optional<Node> toAst() {
        return Optional.of(wrappedNode);
    }

}
