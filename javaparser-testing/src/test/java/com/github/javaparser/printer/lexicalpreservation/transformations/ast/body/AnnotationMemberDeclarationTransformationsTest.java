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

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.AnnotationMemberDeclaration;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.MemberValuePair;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.expr.NormalAnnotationExpr;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.printer.lexicalpreservation.AbstractLexicalPreservingTest;
import org.junit.Test;

import java.io.IOException;
import java.util.EnumSet;

import static org.junit.Assert.assertEquals;

/**
 * Transforming AnnotationMemberDeclaration and verifying the LexicalPreservation works as expected.
 */
public class AnnotationMemberDeclarationTransformationsTest extends AbstractLexicalPreservingTest {

    protected AnnotationMemberDeclaration consider(String code) {
        considerCode("@interface AD { " + code + " }");
        return (AnnotationMemberDeclaration)cu.getAnnotationDeclarationByName("AD").get().getMember(0);
    }

    // Name

    @Test
    public void changingName() throws IOException {
        AnnotationMemberDeclaration md = consider("int foo();");
        md.setName("bar");
        assertTransformedToString("int bar();", md);
    }

    // Type

    @Test
    public void changingType() throws IOException {
        AnnotationMemberDeclaration md = consider("int foo();");
        md.setType("String");
        assertTransformedToString("String foo();", md);
    }

    // Modifiers

    @Test
    public void addingModifiers() throws IOException {
        AnnotationMemberDeclaration md = consider("int foo();");
        md.setModifiers(EnumSet.of(Modifier.PUBLIC));
        assertTransformedToString("public int foo();", md);
    }

    @Test
    public void removingModifiers() throws IOException {
        AnnotationMemberDeclaration md = consider("public int foo();");
        md.setModifiers(EnumSet.noneOf(Modifier.class));
        assertTransformedToString("int foo();", md);
    }

    @Test
    public void replacingModifiers() throws IOException {
        AnnotationMemberDeclaration md = consider("public int foo();");
        md.setModifiers(EnumSet.of(Modifier.PROTECTED));
        assertTransformedToString("protected int foo();", md);
    }

    // Default value

    @Test
    public void addingDefaultValue() throws IOException {
        AnnotationMemberDeclaration md = consider("int foo();");
        md.setDefaultValue(new IntegerLiteralExpr("10"));
        assertTransformedToString("int foo() default 10;", md);
    }

    @Test
    public void removingDefaultValue() throws IOException {
        AnnotationMemberDeclaration md = consider("int foo() default 10;");
        assertEquals(true, md.getDefaultValue().get().remove());
        assertTransformedToString("int foo();", md);
    }

    @Test
    public void replacingDefaultValue() throws IOException {
        AnnotationMemberDeclaration md = consider("int foo() default 10;");
        md.setDefaultValue(new IntegerLiteralExpr("11"));
        assertTransformedToString("int foo() default 11;", md);
    }

    // Annotations

    @Test
    public void addingAnnotation() throws IOException {
        AnnotationMemberDeclaration it = consider("int foo();");
        it.addAnnotation("myAnno");
        assertTransformedToString("@myAnno()\nint foo();", it);
    }

    @Test
    public void removingAnnotationOnSomeLine() throws IOException {
        AnnotationMemberDeclaration it = consider("@myAnno int foo();");
        it.getAnnotations().remove(0);
        assertTransformedToString("int foo();", it);
    }

    @Test
    public void removingAnnotationOnPrevLine() throws IOException {
        AnnotationMemberDeclaration it = consider("@myAnno\nint foo();");
        it.getAnnotations().remove(0);
        assertTransformedToString("int foo();", it);
    }

    @Test
    public void replacingAnnotation() throws IOException {
        AnnotationMemberDeclaration it = consider("@myAnno int foo();");
        it.getAnnotations().set(0, new NormalAnnotationExpr(new Name("myOtherAnno"), new NodeList<>()));
        assertTransformedToString("@myOtherAnno()\nint foo();", it);
    }

    // Javadoc

}
