/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2024 The JavaParser Team.
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
package com.github.javaparser.ast.visitor.equals;

import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.visitor.EqualsVisitor;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

import java.util.stream.Stream;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

class EqualsVisitorCommentTest extends EqualsVisitorTest
{
    private static final String COMMENT = "//line comment\n" + "/* block comment */" + "/** javadoc comment **/";

    public static Stream<Arguments> commentTypes()
    {
        return Stream.of(Arguments.of(LineComment.class), Arguments.of(BlockComment.class), Arguments.of(JavadocComment.class));
    }

    @Test
    void equals_sameComment_true()
    {
        parseAndClone(COMMENT);
        boolean result = EqualsVisitor.equals(nodeLeft, nodeRight);
        assertThat(result, is(true));
    }

    @ParameterizedTest
    @MethodSource("commentTypes")
    void equals_differentLineComment_false(Class<Comment> commentType)
    {
        parseAndClone(COMMENT);
        Comment comment = nodeRight.findFirst(commentType).get();
        comment.setContent(comment.getContent() + "differentContent");
        boolean result = EqualsVisitor.equals(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }
}
