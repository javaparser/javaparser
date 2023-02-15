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
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.PatternExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserSymbolDeclaration;

import java.util.Collections;
import java.util.List;

/**
 * @author Federico Tomassetti
 */
public class VariableDeclarationExprContext extends AbstractJavaParserContext<VariableDeclarationExpr> {

    public VariableDeclarationExprContext(VariableDeclarationExpr wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name) {
        List<PatternExpr> patternExprs = patternExprsExposedFromChildren();
        for (int i = 0; i < patternExprs.size(); i++) {
            PatternExpr patternExpr = patternExprs.get(i);
            if(patternExpr.getNameAsString().equals(name)) {
                return SymbolReference.solved(JavaParserSymbolDeclaration.patternVar(patternExpr, typeSolver));
            }
        }

        // Default to solving in parent context if unable to solve directly here.
        return solveSymbolInParentContext(name);
    }

    @Override
    public List<VariableDeclarator> localVariablesExposedToChild(Node child) {
        for (int i = 0; i < wrappedNode.getVariables().size(); i++) {
            if (child == wrappedNode.getVariable(i)) {
                return wrappedNode.getVariables().subList(0, i);
            }
        }
        // TODO: Consider pattern exprs
        return Collections.emptyList();
    }



    @Override
    public List<PatternExpr> patternExprsExposedFromChildren() {
        // Variable declarations never make pattern expressions available.
        return Collections.emptyList();
    }

    @Override
    public List<PatternExpr> negatedPatternExprsExposedFromChildren() {
        // Variable declarations never make pattern expressions available.
        return Collections.emptyList();
    }

}
