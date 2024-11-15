/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2024 The JavaParser Team.
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
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.resolution.Context;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.model.Value;
import java.util.Optional;

/**
 * @author Johannes Coetzee
 */
public class ExpressionContext<N extends Expression> extends AbstractJavaParserContext<N> {

    public ExpressionContext(N wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public Optional<Value> solveSymbolAsValue(String name) {
        SymbolReference<? extends ResolvedValueDeclaration> solvedSymbol = solveSymbol(name);
        return solvedSymbol.getDeclaration().map(Value::from);
    }

    @Override
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name) {
        Optional<Node> maybeParent = getParent().map(Context::getWrappedNode);

        if (maybeParent.isPresent()) {
            SymbolReference<? extends ResolvedValueDeclaration> symbolFromPattern =
                    findExposedPatternInParentContext(maybeParent.get(), name);
            if (symbolFromPattern.isSolved()) {
                return symbolFromPattern;
            }
        }

        return solveSymbolInParentContext(name);
    }
}
