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

package org.javaparser.symbolsolver.javaparsermodel.declarators;

import org.javaparser.ast.Node;
import org.javaparser.resolution.declarations.ResolvedValueDeclaration;
import org.javaparser.symbolsolver.model.resolution.TypeSolver;

import java.util.Collections;
import java.util.List;

/**
 * @author Federico Tomassetti
 */
public class NoSymbolDeclarator<N extends Node> extends AbstractSymbolDeclarator<N> {

    public NoSymbolDeclarator(N wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public List<ResolvedValueDeclaration> getSymbolDeclarations() {
        return Collections.emptyList();
    }

}
