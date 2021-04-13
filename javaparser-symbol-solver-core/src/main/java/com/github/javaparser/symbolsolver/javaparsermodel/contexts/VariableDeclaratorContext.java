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

package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.PatternExpr;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

import java.util.Collections;
import java.util.List;

/**
 * @author Federico Tomassetti
 */
public class VariableDeclaratorContext extends AbstractJavaParserContext<VariableDeclarator> {

    public VariableDeclaratorContext(VariableDeclarator wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public List<VariableDeclarator> localVariablesExposedToChild(Node child) {
        if (wrappedNode.getInitializer().isPresent() && wrappedNode.getInitializer().get() == child) {
            return Collections.singletonList(wrappedNode);
        }

        return Collections.emptyList();
    }

    @Override
    public List<PatternExpr> patternExprsExposedFromChildren() {
        // Variable declarators never make pattern expressions available.
        return Collections.emptyList();
    }

    @Override
    public List<PatternExpr> negatedPatternExprsExposedFromChildren() {
        // Variable declarators never make pattern expressions available.
        return Collections.emptyList();
    }

}
