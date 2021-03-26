/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2021 The JavaParser Team.
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

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.resolution.declarations.AssociableToAST;
import com.github.javaparser.resolution.declarations.ResolvedFieldDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedFieldDeclarationTest;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertThrows;

class JavaParserFieldDeclarationTest implements ResolvedFieldDeclarationTest {

    @Test
    void whenTypeSolverIsNullShouldThrowIllegalArgumentException() {
        CompilationUnit compilationUnit = StaticJavaParser.parse("class A {String s;}");
        VariableDeclarator variableDeclarator = compilationUnit.findFirst(FieldDeclaration.class).get()
                .getVariable(0);
        assertThrows(IllegalArgumentException.class,
                () -> new JavaParserFieldDeclaration(variableDeclarator, null));
    }

    //
    //  Initialize ResolvedFieldDeclarationTest
    //

    private static ResolvedFieldDeclaration createResolvedFieldDeclaration(boolean isStatic) {
        String code = isStatic ? "class A {static String s;}" : "class A {String s;}";
        FieldDeclaration fieldDeclaration = StaticJavaParser.parse(code)
                .findFirst(FieldDeclaration.class).get();
        ReflectionTypeSolver reflectionTypeSolver = new ReflectionTypeSolver();
        return new JavaParserFieldDeclaration(fieldDeclaration.getVariable(0), reflectionTypeSolver);
    }

    @Override
    public ResolvedFieldDeclaration createValue() {
        return createResolvedFieldDeclaration(false);
    }

    @Override
    public ResolvedFieldDeclaration createStaticValue() {
        return createResolvedFieldDeclaration(true);
    }

    @Override
    public Optional<FieldDeclaration> getWrappedDeclaration(AssociableToAST<FieldDeclaration> associableToAST) {
        return Optional.of(
                safeCast(associableToAST, JavaParserFieldDeclaration.class).getWrappedNode()
        );
    }

    @Override
    public String getCanonicalNameOfExpectedType(ResolvedValueDeclaration resolvedDeclaration) {
        return String.class.getCanonicalName();
    }

}
