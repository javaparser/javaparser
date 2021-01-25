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

package com.github.javaparser.symbolsolver.javaparsermodel.declarators;

import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserSymbolDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
public class VariableSymbolDeclarator extends AbstractSymbolDeclarator<VariableDeclarationExpr> {

    public VariableSymbolDeclarator(VariableDeclarationExpr wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
        wrappedNode.getParentNode().ifPresent(p -> {
            if (p instanceof FieldDeclaration) {
                throw new IllegalArgumentException();
            }
        });
    }

    @Override
    public List<ResolvedValueDeclaration> getSymbolDeclarations() {
        List<ResolvedValueDeclaration> variables = wrappedNode.getVariables()
                .stream()
                .map(v -> JavaParserSymbolDeclaration.localVar(v, typeSolver))
                .collect(Collectors.toCollection(ArrayList::new));

//        // FIXME: This returns ALL PatternExpr, regardless of whether it is in scope or not.
//        List<JavaParserSymbolDeclaration> patterns = wrappedNode.getVariables()
//                .stream()
//                .filter(variableDeclarator -> variableDeclarator.getInitializer().isPresent())
//                .map(variableDeclarator -> variableDeclarator.getInitializer().get())
//                .map(expression -> expression.findAll(PatternExpr.class))
//                .flatMap(Collection::stream)
//                .map(v -> JavaParserSymbolDeclaration.patternVar(v, typeSolver))
//                .collect(Collectors.toCollection(ArrayList::new));

        List<ResolvedValueDeclaration> all = new ArrayList<>(variables);
//        all.addAll(patterns);

        return all;
    }

}
