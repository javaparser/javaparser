/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
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

package com.github.javaparser.printer.lexicalpreservation.transformations.ast.body;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.printer.lexicalpreservation.AbstractLexicalPreservingTest;
import org.junit.Test;

import java.io.IOException;
import java.util.EnumSet;

/**
 * Transforming MethodDeclaration and verifying the LexicalPreservation works as expected.
 */
public class MethodDeclarationTransformationsTest extends AbstractLexicalPreservingTest {

    protected MethodDeclaration consider(String code) {
        considerCode("class A { " + code + " }");
        return cu.getType(0).getMembers().get(0).asMethodDeclaration();
    }

    // Name

    @Test
    public void settingName() throws IOException {
        MethodDeclaration it = consider("void A(){}");
        it.setName("B");
        assertTransformedToString("void B(){}", it);
    }

    // JavaDoc

    // Modifiers

    @Test
    public void addingModifiers() throws IOException {
        MethodDeclaration it = consider("void A(){}");
        it.setModifiers(EnumSet.of(Modifier.PUBLIC));
        assertTransformedToString("public void A(){}", it);
    }

    @Test
    public void removingModifiers() throws IOException {
        MethodDeclaration it = consider("public void A(){}");
        it.setModifiers(EnumSet.noneOf(Modifier.class));
        assertTransformedToString("void A(){}", it);
    }

    @Test
    public void replacingModifiers() throws IOException {
        MethodDeclaration it = consider("public void A(){}");
        it.setModifiers(EnumSet.of(Modifier.PROTECTED));
        assertTransformedToString("protected void A(){}", it);
    }

    // Parameters

    @Test
    public void addingParameters() throws IOException {
        MethodDeclaration it = consider("void foo(){}");
        it.addParameter(PrimitiveType.doubleType(), "d");
        assertTransformedToString("void foo(double d){}", it);
    }

    @Test
    public void removingOnlyParameter() throws IOException {
        MethodDeclaration it = consider("public void foo(double d){}");
        it.getParameters().remove(0);
        assertTransformedToString("public void foo(){}", it);
    }

    @Test
    public void removingFirstParameterOfMany() throws IOException {
        MethodDeclaration it = consider("public void foo(double d, float f){}");
        it.getParameters().remove(0);
        assertTransformedToString("public void foo(float f){}", it);
    }

    @Test
    public void removingLastParameterOfMany() throws IOException {
        MethodDeclaration it = consider("public void foo(double d, float f){}");
        it.getParameters().remove(1);
        assertTransformedToString("public void foo(double d){}", it);
    }

    @Test
    public void replacingOnlyParameter() throws IOException {
        MethodDeclaration it = consider("public void foo(float f){}");
        it.getParameters().set(0, new Parameter(new ArrayType(PrimitiveType.intType()), new SimpleName("foo")));
        assertTransformedToString("public void foo(int[] foo){}", it);
    }

    // ThrownExceptions

    // Body

    // Annotations
}
