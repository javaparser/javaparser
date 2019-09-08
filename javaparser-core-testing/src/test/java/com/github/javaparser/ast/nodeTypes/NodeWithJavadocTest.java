/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2017 The JavaParser Team.
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

package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.comments.LineComment;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class NodeWithJavadocTest {

    @Test
    void removeJavaDocNegativeCaseNoComment() {
        ClassOrInterfaceDeclaration decl = new ClassOrInterfaceDeclaration(new NodeList<>(),
                false, "Foo");
        assertFalse(decl.removeJavaDocComment());
    }

    @Test
    void removeJavaDocNegativeCaseCommentNotJavaDoc() {
        ClassOrInterfaceDeclaration decl = new ClassOrInterfaceDeclaration(new NodeList<>(),
                false, "Foo");
        decl.setComment(new LineComment("A comment"));
        assertFalse(decl.removeJavaDocComment());
        assertTrue(decl.getComment().isPresent());
    }

    @Test
    void removeJavaDocPositiveCase() {
        ClassOrInterfaceDeclaration decl = new ClassOrInterfaceDeclaration(new NodeList<>(),
                false, "Foo");
        decl.setComment(new JavadocComment("A comment"));
        assertTrue(decl.removeJavaDocComment());
        assertFalse(decl.getComment().isPresent());
    }

    @Test
    void getJavadocOnMethodWithLineCommentShouldReturnEmptyOptional() {
        MethodDeclaration method = new MethodDeclaration();
        method.setLineComment("Lorem Ipsum.");

        assertFalse(method.getJavadocComment().isPresent());
        assertFalse(method.getJavadoc().isPresent());
    }

}