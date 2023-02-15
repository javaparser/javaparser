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

import com.github.javaparser.ast.body.EnumConstantDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserEnumConstantDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserEnumDeclaration;

import java.util.List;

/**
 * @author Federico Tomassetti
 */
public class EnumDeclarationContext extends AbstractJavaParserContext<EnumDeclaration> {

    private JavaParserTypeDeclarationAdapter javaParserTypeDeclarationAdapter;

    public EnumDeclarationContext(EnumDeclaration wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
        this.javaParserTypeDeclarationAdapter = new JavaParserTypeDeclarationAdapter(wrappedNode, typeSolver,
                getDeclaration(), this);
    }

    @Override
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name) {
        if (typeSolver == null) throw new IllegalArgumentException();

        // among constants
        for (EnumConstantDeclaration constant : wrappedNode.getEntries()) {
            if (constant.getName().getId().equals(name)) {
                return SymbolReference.solved(new JavaParserEnumConstantDeclaration(constant, typeSolver));
            }
        }

        if (this.getDeclaration().hasField(name)) {
            return SymbolReference.solved(this.getDeclaration().getField(name));
        }

        // then to parent
        return solveSymbolInParentContext(name);
    }

    @Override
    public SymbolReference<ResolvedTypeDeclaration> solveType(String name, List<ResolvedType> resolvedTypes) {
        return javaParserTypeDeclarationAdapter.solveType(name, resolvedTypes);
    }

    @Override
    public SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> argumentsTypes, boolean staticOnly) {
        return javaParserTypeDeclarationAdapter.solveMethod(name, argumentsTypes, staticOnly);
    }

    ///
    /// Private methods
    ///

    private ResolvedReferenceTypeDeclaration getDeclaration() {
        return new JavaParserEnumDeclaration(this.wrappedNode, typeSolver);
    }
}
