/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2025 The JavaParser Team.
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
package com.github.javaparser.ast.comments;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * https://openjdk.org/jeps/467 added support for markdown JavaDoc comments
 * /// That are prefixed with ///
 * /// Support `markdown` markup and references
 * /// And supports substrings not allowed in regular block comments, e.g. *_no_space_here_/
 * <p>
 * While these comments could be seen as a series of single line comments, they are functionally block comments.
 * The {@code MarkdownComment} class adds support for this, although special handling is required for the content
 * of these comments, since the header is no longer only applied to the start of the comment, but rather to the
 * start of each line.
 */
public class MarkdownComment extends Comment {

    public MarkdownComment() {
        this(null, "empty");
    }

    @AllFieldsConstructor
    public MarkdownComment(String content) {
        this(null, content);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public MarkdownComment(TokenRange tokenRange, String content) {
        super(tokenRange, content);
        customInitialization();
    }

    @Override
    public String getHeader() {
        return "///";
    }

    @Override
    public String getFooter() {
        return "";
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return null;
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {

    }

    @Override
    public String asString() {
        // Return sensible string here
        return getContent();
    }
}
