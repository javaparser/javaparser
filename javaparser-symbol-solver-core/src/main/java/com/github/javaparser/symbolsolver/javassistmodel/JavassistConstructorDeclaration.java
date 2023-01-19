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

package com.github.javaparser.symbolsolver.javassistmodel;

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedParameterDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import javassist.CtConstructor;

import java.util.List;

/**
 * @author Fred Lefévère-Laoide
 */
public class JavassistConstructorDeclaration implements ResolvedConstructorDeclaration {
    private final CtConstructor ctConstructor;
    private final TypeSolver typeSolver;
    private final JavassistMethodLikeDeclarationAdapter methodLikeAdaper;

    public JavassistConstructorDeclaration(CtConstructor ctConstructor, TypeSolver typeSolver) {
        this.ctConstructor = ctConstructor;
        this.typeSolver = typeSolver;
        this.methodLikeAdaper = new JavassistMethodLikeDeclarationAdapter(ctConstructor, typeSolver, this);
    }

    @Override
    public String toString() {
        return getClass().getSimpleName() + "{" +
                "ctConstructor=" + ctConstructor.getName() +
                ", typeSolver=" + typeSolver +
                '}';
    }

    @Override
    public String getName() {
        return ctConstructor.getName();
    }

    @Override
    public boolean isField() {
        return false;
    }

    @Override
    public boolean isParameter() {
        return false;
    }

    @Override
    public boolean isType() {
        return false;
    }

    @Override
    public ResolvedReferenceTypeDeclaration declaringType() {
        return JavassistFactory.toTypeDeclaration(ctConstructor.getDeclaringClass(), typeSolver);
    }

    @Override
    public int getNumberOfParams() {
        return methodLikeAdaper.getNumberOfParams();
    }

    @Override
    public ResolvedParameterDeclaration getParam(int i) {
        return methodLikeAdaper.getParam(i);
    }

    @Override
    public List<ResolvedTypeParameterDeclaration> getTypeParameters() {
        return methodLikeAdaper.getTypeParameters();
    }

    @Override
    public AccessSpecifier accessSpecifier() {
        return JavassistFactory.modifiersToAccessLevel(ctConstructor.getModifiers());
    }

    @Override
    public int getNumberOfSpecifiedExceptions() {
        return methodLikeAdaper.getNumberOfSpecifiedExceptions();
    }

    @Override
    public ResolvedType getSpecifiedException(int index) {
        return methodLikeAdaper.getSpecifiedException(index);
    }

}
