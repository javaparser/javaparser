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

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedParameterDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;

import java.util.Collections;
import java.util.List;

/**
 * This represents the default constructor added by the compiler for objects not declaring one.
 * It takes no parameters. See JLS 8.8.9 for details.
 *
 * @author Federico Tomassetti
 */
public class DefaultConstructorDeclaration<N extends ResolvedReferenceTypeDeclaration> implements ResolvedConstructorDeclaration {

    private N declaringType;

    DefaultConstructorDeclaration(N declaringType) {
        this.declaringType = declaringType;
    }

    @Override
    public N declaringType() {
        return declaringType;
    }

    @Override
    public int getNumberOfParams() {
        return 0;
    }

    @Override
    public ResolvedParameterDeclaration getParam(int i) {
        throw new UnsupportedOperationException("The default constructor has no parameters");
    }

    @Override
    public String getName() {
        return declaringType.getName();
    }

    @Override
    public AccessSpecifier accessSpecifier() {
        return AccessSpecifier.PUBLIC;
    }

    @Override
    public List<ResolvedTypeParameterDeclaration> getTypeParameters() {
        return Collections.emptyList();
    }

    @Override
    public int getNumberOfSpecifiedExceptions() {
        return 0;
    }

    @Override
    public ResolvedType getSpecifiedException(int index) {
        throw new UnsupportedOperationException("The default constructor does not throw exceptions");
    }

}
