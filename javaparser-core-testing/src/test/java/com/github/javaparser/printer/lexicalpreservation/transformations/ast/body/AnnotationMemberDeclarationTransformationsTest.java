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

import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.AnnotationMemberDeclaration;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.expr.NormalAnnotationExpr;
import com.github.javaparser.printer.lexicalpreservation.AbstractLexicalPreservingTest;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.ast.Modifier.Keyword.PROTECTED;
import static com.github.javaparser.ast.Modifier.Keyword.PUBLIC;
import static com.github.javaparser.ast.Modifier.createModifierList;
import static com.github.javaparser.utils.Utils.EOL;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Transforming AnnotationMemberDeclaration and verifying the LexicalPreservation works as expected.
 */
class AnnotationMemberDeclarationTransformationsTest extends AbstractLexicalPreservingTest {

    protected AnnotationMemberDeclaration consider(String code) {
        considerCode("@interface AD { " + code + " }");
        return cu.getAnnotationDeclarationByName("AD").get().getMember(0).asAnnotationMemberDeclaration();
    }

    // Name

    @Test
    void changingName() {
        AnnotationMemberDeclaration md = consider("int foo();");
        md.setName("bar");
        assertTransformedToString("int bar();", md);
    }

    // Type

    @Test
    void changingType() {
        AnnotationMemberDeclaration md = consider("int foo();");
        md.setType("String");
        assertTransformedToString("String foo();", md);
    }

    // Modifiers

    @Test
    void addingModifiers() {
        AnnotationMemberDeclaration md = consider("int foo();");
        md.setModifiers(createModifierList(PUBLIC));
        assertTransformedToString("public int foo();", md);
    }

    @Test
    void removingModifiers() {
        AnnotationMemberDeclaration md = consider("public int foo();");
        md.setModifiers(new NodeList<>());
        assertTransformedToString("int foo();", md);
    }

    @Test
    void replacingModifiers() {
        AnnotationMemberDeclaration md = consider("public int foo();");
        md.setModifiers(createModifierList(PROTECTED));
        assertTransformedToString("protected int foo();", md);
    }

    // Default value

    @Test
    void addingDefaultValue() {
        AnnotationMemberDeclaration md = consider("int foo();");
        md.setDefaultValue(new IntegerLiteralExpr("10"));
        assertTransformedToString("int foo() default 10;", md);
    }

    @Test
    void removingDefaultValue() {
        AnnotationMemberDeclaration md = consider("int foo() default 10;");
        assertTrue(md.getDefaultValue().get().remove());
        assertTransformedToString("int foo();", md);
    }

    @Test
    void replacingDefaultValue() {
        AnnotationMemberDeclaration md = consider("int foo() default 10;");
        md.setDefaultValue(new IntegerLiteralExpr("11"));
        assertTransformedToString("int foo() default 11;", md);
    }

    // Annotations

    @Test
    void addingAnnotation() {
        AnnotationMemberDeclaration it = consider("int foo();");
        it.addAnnotation("myAnno");
        assertTransformedToString("@myAnno()" + EOL + "int foo();", it);
    }

    @Test
    void addingTwoAnnotations() {
        AnnotationMemberDeclaration it = consider("int foo();");
        it.addAnnotation("myAnno");
        it.addAnnotation("myAnno2");
        assertTransformedToString("@myAnno()" + EOL + "@myAnno2()" + EOL + "int foo();", it);
    }

    @Test
    void removingAnnotationOnSomeLine() {
        AnnotationMemberDeclaration it = consider("@myAnno int foo();");
        it.getAnnotations().remove(0);
        assertTransformedToString("int foo();", it);
    }

    @Test
    void removingAnnotationOnPrevLine() {
        AnnotationMemberDeclaration it = consider("@myAnno" + EOL + "int foo();");
        it.getAnnotations().remove(0);
        assertTransformedToString("int foo();", it);
    }

    @Test
    void replacingAnnotation() {
        AnnotationMemberDeclaration it = consider("@myAnno int foo();");
        it.getAnnotations().set(0, new NormalAnnotationExpr(new Name("myOtherAnno"), new NodeList<>()));
        assertTransformedToString("@myOtherAnno() int foo();", it);
    }

    // Javadoc

    @Test
    void addingJavadoc() {
        AnnotationMemberDeclaration it = consider("int foo();");
        it.setJavadocComment("Cool this annotation!");
        assertTransformedToString("@interface AD { /**Cool this annotation!*/" + EOL +
                "int foo(); }", it.getParentNode().get());
    }

    @Test
    void removingJavadoc() {
        AnnotationMemberDeclaration it = consider("/**Cool this annotation!*/ int foo();");
        assertTrue(it.getJavadocComment().get().remove());
        assertTransformedToString("@interface AD {  int foo(); }", it.getParentNode().get());
    }

    @Test
    void replacingJavadoc() {
        AnnotationMemberDeclaration it = consider("/**Cool this annotation!*/ int foo();");
        it.setJavadocComment("Super extra cool this annotation!!!");
        assertTransformedToString("@interface AD { /**Super extra cool this annotation!!!*/ int foo(); }", it.getParentNode().get());
    }

}
