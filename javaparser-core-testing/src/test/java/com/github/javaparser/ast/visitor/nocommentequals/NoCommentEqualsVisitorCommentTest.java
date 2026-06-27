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
package com.github.javaparser.ast.visitor.nocommentequals;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.comments.MarkdownComment;
import com.github.javaparser.ast.comments.TraditionalJavadocComment;
import com.github.javaparser.ast.visitor.NoCommentEqualsVisitor;
import com.github.javaparser.ast.visitor.Visitable;
import com.github.javaparser.ast.visitor.equals.EqualsVisitorTest;
import org.junit.jupiter.api.Test;

public class NoCommentEqualsVisitorCommentTest extends EqualsVisitorTest {

    @Override
    protected boolean equalsNodes(Node n, Node n2) {
        return NoCommentEqualsVisitor.equals(n, n2);
    }

    private NoCommentEqualsVisitor visitor() throws Exception {
        java.lang.reflect.Field f = NoCommentEqualsVisitor.class.getDeclaredField("SINGLETON");
        f.setAccessible(true);
        return (NoCommentEqualsVisitor) f.get(null);
    }

    @Test
    void visit_lineComment_alwaysTrue() throws Exception {
        LineComment left = new LineComment("hello");
        LineComment right = new LineComment("different");
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(true));
    }

    @Test
    void visit_blockComment_alwaysTrue() throws Exception {
        BlockComment left = new BlockComment("hello");
        BlockComment right = new BlockComment("different");
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(true));
    }

    @Test
    void visit_javadocComment_alwaysTrue() throws Exception {
        TraditionalJavadocComment left = new TraditionalJavadocComment("hello");
        TraditionalJavadocComment right = new TraditionalJavadocComment("different");
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(true));
    }

    @Test
    void visit_markdownComment_sameContent_true() throws Exception {
        MarkdownComment left = new MarkdownComment("hello");
        MarkdownComment right = new MarkdownComment("hello");
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(true));
    }

    @Test
    void visit_markdownComment_differentContent_false() throws Exception {
        MarkdownComment left = new MarkdownComment("hello");
        MarkdownComment right = new MarkdownComment("different");
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(false));
    }
}
