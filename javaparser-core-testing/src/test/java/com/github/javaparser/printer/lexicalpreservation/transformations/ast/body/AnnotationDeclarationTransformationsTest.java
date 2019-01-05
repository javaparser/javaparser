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
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.printer.lexicalpreservation.AbstractLexicalPreservingTest;
import org.junit.jupiter.api.Test;

import java.io.IOException;

import static com.github.javaparser.ast.Modifier.Keyword.PROTECTED;
import static com.github.javaparser.ast.Modifier.Keyword.PUBLIC;
import static com.github.javaparser.ast.Modifier.createModifierList;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Transforming AnnotationDeclaration and verifying the LexicalPreservation works as expected.
 */
class AnnotationDeclarationTransformationsTest extends AbstractLexicalPreservingTest {

    @Test
    void unchangedExamples() throws IOException {
        assertUnchanged("AnnotationDeclaration_Example1");
        assertUnchanged("AnnotationDeclaration_Example3");
        assertUnchanged("AnnotationDeclaration_Example9");
    }

    // name

    @Test
    void changingName() throws IOException {
        considerExample("AnnotationDeclaration_Example1_original");
        cu.getAnnotationDeclarationByName("ClassPreamble").get().setName("NewName");
        assertTransformed("AnnotationDeclaration_Example1", cu);
    }

    // modifiers

    @Test
    void addingModifiers() throws IOException {
        considerExample("AnnotationDeclaration_Example1_original");
        cu.getAnnotationDeclarationByName("ClassPreamble").get().setModifiers(createModifierList(PUBLIC));
        assertTransformed("AnnotationDeclaration_Example2", cu);
    }

    @Test
    void removingModifiers() throws IOException {
        considerExample("AnnotationDeclaration_Example3_original");
        cu.getAnnotationDeclarationByName("ClassPreamble").get().setModifiers(new NodeList<>());
        assertTransformed("AnnotationDeclaration_Example3", cu);
    }

    @Test
    void replacingModifiers() throws IOException {
        considerExample("AnnotationDeclaration_Example3_original");
        cu.getAnnotationDeclarationByName("ClassPreamble").get().setModifiers(createModifierList(PROTECTED));
        assertTransformed("AnnotationDeclaration_Example4", cu);
    }

    // members

    @Test
    void addingMember() throws IOException {
        considerExample("AnnotationDeclaration_Example3_original");
        cu.getAnnotationDeclarationByName("ClassPreamble").get().addMember(new AnnotationMemberDeclaration(new NodeList<>(), PrimitiveType.intType(), "foo", null));
        assertTransformed("AnnotationDeclaration_Example5", cu);
    }

    @Test
    void removingMember() throws IOException {
        considerExample("AnnotationDeclaration_Example3_original");
        cu.getAnnotationDeclarationByName("ClassPreamble").get().getMember(2).remove();
        assertTransformed("AnnotationDeclaration_Example6", cu);
    }

    @Test
    void replacingMember() throws IOException {
        considerExample("AnnotationDeclaration_Example3_original");
        cu.getAnnotationDeclarationByName("ClassPreamble").get().setMember(2, new AnnotationMemberDeclaration(new NodeList<>(), PrimitiveType.intType(), "foo", null));
        assertTransformed("AnnotationDeclaration_Example7", cu);
    }

    // javadoc

    @Test
    void addingJavadoc() throws IOException {
        considerExample("AnnotationDeclaration_Example3_original");
        cu.getAnnotationDeclarationByName("ClassPreamble").get().setJavadocComment("Cool this annotation!");
        assertTransformed("AnnotationDeclaration_Example8", cu);
    }

    @Test
    void removingJavadoc() throws IOException {
        considerExample("AnnotationDeclaration_Example9_original");
        boolean removed = cu.getAnnotationDeclarationByName("ClassPreamble").get().getJavadocComment().get().remove();
        assertTrue(removed);
        assertTransformed("AnnotationDeclaration_Example9", cu);
    }

    @Test
    void replacingJavadoc() throws IOException {
        considerExample("AnnotationDeclaration_Example9_original");
        cu.getAnnotationDeclarationByName("ClassPreamble").get().setJavadocComment("Super extra cool this annotation!!!");
        assertTransformed("AnnotationDeclaration_Example10", cu);
    }

}
