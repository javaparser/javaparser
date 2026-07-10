/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
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

package com.github.javaparser.ast.visitor;

import static com.github.javaparser.StaticJavaParser.parse;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import java.util.stream.Stream;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

class NoCommentEqualsVisitorTest {

    @Test
    void testEquals() {
        CompilationUnit p1 = parse("class X { }");
        CompilationUnit p2 = parse("class X { }");
        assertTrue(NoCommentEqualsVisitor.equals(p1, p2));
    }

    @Test
    void testEqualsWithDifferentComments() {
        CompilationUnit p1 = parse("/* a */ class X { /** b */} //c");
        CompilationUnit p2 = parse("/* b */ class X { }  //c");
        assertTrue(NoCommentEqualsVisitor.equals(p1, p2));
    }

    @Test
    void testNotEquals() {
        CompilationUnit p1 = parse("class X { }");
        CompilationUnit p2 = parse("class Y { }");
        assertFalse(NoCommentEqualsVisitor.equals(p1, p2));
    }

    static Stream<BaseNodeMetaModel> provideConcreteCommentMetamodels() {
        return JavaParserMetaModel.getNodeMetaModels().stream()
                .filter(meta -> Comment.class.isAssignableFrom(meta.getType()))
                .filter(meta -> !meta.isAbstract());
    }

    @ParameterizedTest(name = "Ignore comment for node type: {0}")
    @MethodSource("provideConcreteCommentMetamodels")
    @DisplayName("No-Comment equals visitor must unconditionally ignore content of any type of comments")
    void noCommentVisitors_MustUnconditionallyIgnoreAnyMetamodelCommentSubtypes(BaseNodeMetaModel meta) {
        Class<? extends Comment> commentClass = (Class<? extends Comment>) meta.getType();

        Comment commentLeft = createCommentInstance(commentClass, "Content Alpha");
        Comment commentRight = createCommentInstance(commentClass, "Content Omega");

        boolean equalsResult = NoCommentEqualsVisitor.equals(commentLeft, commentRight);

        String commentTypeName = commentClass.getSimpleName();
        assertTrue(
                equalsResult,
                String.format(
                        "NoCommentEqualsVisitor failed for %s. It evaluated the content instead of skipping the node.",
                        commentTypeName));
    }

    private Comment createCommentInstance(Class<? extends Comment> type, String content) {
        try {
            return type.getConstructor(String.class).newInstance(content);
        } catch (Exception e) {
            throw new RuntimeException("Failed to dynamically instantiate comment type: " + type.getName(), e);
        }
    }
}
