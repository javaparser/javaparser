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

package org.javaparser.symbolsolver.javaparsermodel.contexts;

import org.javaparser.ast.Node;
import org.javaparser.ast.body.Parameter;
import org.javaparser.ast.body.VariableDeclarator;
import org.javaparser.ast.stmt.CatchClause;
import org.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import org.javaparser.resolution.declarations.ResolvedValueDeclaration;
import org.javaparser.resolution.types.ResolvedType;
import org.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import org.javaparser.symbolsolver.model.resolution.SymbolReference;
import org.javaparser.symbolsolver.model.resolution.TypeSolver;
import org.javaparser.symbolsolver.model.resolution.Value;
import org.javaparser.symbolsolver.resolution.SymbolDeclarator;

import java.util.Collections;
import java.util.List;
import java.util.Optional;

/**
 * @author Fred Lefévère-Laoide
 */
public class CatchClauseContext extends AbstractJavaParserContext<CatchClause> {

    public CatchClauseContext(CatchClause wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    public final SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name) {
        SymbolDeclarator sb = JavaParserFactory.getSymbolDeclarator(wrappedNode.getParameter(), typeSolver);
        SymbolReference<? extends ResolvedValueDeclaration> symbolReference = AbstractJavaParserContext.solveWith(sb, name);
        if (symbolReference.isSolved()) {
            return symbolReference;
        }

        // if nothing is found we should ask the parent context
        return getParent().solveSymbol(name);
    }

    @Override
    public final Optional<Value> solveSymbolAsValue(String name) {
        SymbolDeclarator sb = JavaParserFactory.getSymbolDeclarator(wrappedNode.getParameter(), typeSolver);
        Optional<Value> symbolReference = solveWithAsValue(sb, name);
        if (symbolReference.isPresent()) {
            // Perform parameter type substitution as needed
            return symbolReference;
        }

        // if nothing is found we should ask the parent context
        return getParent().solveSymbolAsValue(name);
    }

    @Override
    public final SymbolReference<ResolvedMethodDeclaration> solveMethod(
            String name, List<ResolvedType> argumentsTypes, boolean staticOnly) {
        return getParent().solveMethod(name, argumentsTypes, false);
    }

    @Override
    public List<VariableDeclarator> localVariablesExposedToChild(Node child) {
        return Collections.emptyList();
    }

    @Override
    public List<Parameter> parametersExposedToChild(Node child) {
        if (child == getWrappedNode().getBody()) {
            return Collections.singletonList(getWrappedNode().getParameter());
        }
        return Collections.emptyList();
    }
}
