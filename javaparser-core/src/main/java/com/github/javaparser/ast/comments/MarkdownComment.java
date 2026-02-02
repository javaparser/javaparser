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
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.MarkdownCommentMetaModel;
import com.github.javaparser.utils.LineSeparator;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Optional;
import java.util.function.Consumer;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

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
public class MarkdownComment extends JavadocComment {

    private static Pattern markdownLinePattern = Pattern.compile("^\\s*///(.*)$");

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

    /**
     * Returns the Markdown content of this comment as defined in <a href="https://openjdk.org/jeps/467">JEP 467</a>:
     * <blockquote cite="https://openjdk.org/jeps/467">
     *     Because horizontal whitespace at the beginning and end of each line of Markdown text may be significant,
     *     the content of a Markdown documentation comment is determined as follows:
     *     -- Any leading whitespace and the three initial / characters are removed from each line.
     *     -- The lines are shifted left, by removing leading whitespace characters, until the non-blank line with the
     *        least leading whitespace has no remaining leading whitespace.
     *     -- Additional leading whitespace and any trailing whitespace in each line is preserved, because it may be
     *        significant. For example, whitespace at the beginning of a line may indicate an indented code block or the
     *        continuation of a list item, and whitespace at the end of a line may indicate a hard line break.
     *     </blockquote>
     */
    public String getMarkdownContent() {
        String content = getContent();
        // Start by isolating the lines to make calculating and stripping leading whitespace easier
        ArrayList<String> commentLines = new ArrayList<>();
        commentLines.addAll(Arrays.asList(content.split("(\r\n|\r|\n)")));
        ArrayList<String> formattedLines = new ArrayList<>();
        for (String line : commentLines) {
            // Use pattern matching to strip leading whitespace followed by /// for each of the lines.
            Matcher matcher = markdownLinePattern.matcher(line);
            if (matcher.matches()) {
                formattedLines.add(matcher.group(1));
            } else {
                formattedLines.add(line);
            }
        }
        // Find the length of the shortest whitespace prefix for all the lines so that this can be stripped according
        // to the Java specification. For example, treating . as whitespace in the example below, 2 spaces will be
        // stripped:
        // ///....prefix_length=4
        // ///......prefix_length=8
        // ///..prefix_length=2
        int shortestWhitespacePrefix = Integer.MAX_VALUE;
        for (String line : formattedLines) {
            for (int i = 0; i < line.length(); i++) {
                if (!Character.isWhitespace(line.charAt(i))) {
                    shortestWhitespacePrefix = Math.min(shortestWhitespacePrefix, i);
                    break;
                }
            }
        }
        StringBuilder contentBuilder = new StringBuilder();
        LineSeparator lineSeparator = LineSeparator.detect(content);
        // Reassemble the content with the whitespace prefix stripped and without adding back the /// removed by the
        // pattern match above.
        for (int i = 0; i < formattedLines.size(); i++) {
            String line = formattedLines.get(i);
            if (line.trim().isEmpty()) {
                contentBuilder.append(line);
            } else {
                contentBuilder.append(line.substring(shortestWhitespacePrefix));
            }
            if (i != formattedLines.size() - 1) {
                contentBuilder.append(lineSeparator.asRawString());
            }
        }
        return contentBuilder.toString();
    }

    /**
     * For other comment types, the header is the character sequence that starts the comment, i.e. /* for block
     * comments and // for line comments and the footer is the character sequence that ends the comment, i.e. * / for
     * block comments, but empty for line comments. These comments can then be reconstructed with
     *   c.getHeader() + c.getContent() + c.getFooter().
     * For Markdown comments, this model doesn't fit as well, since the header is now a character sequence that
     * appears at the start of each line. For ease of use, the leading /// is now included in the comment content,
     * returned by the getContent() method, while the getMarkdownContent() method returns the comment content with the
     * leading /// stripped from each line.
     *
     * @return the empty string
     */
    @Override
    public String getHeader() {
        return "";
    }

    /**
     * Markdown comments are not terminated by a specific character sequence, so just use the empty string as a footer.
     * @return the empty string
     */
    @Override
    public String getFooter() {
        return "";
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.AcceptGenerator")
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.AcceptGenerator")
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    @Override
    public String asString() {
        String content = getContent();
        // Try to preserve line separators
        String lineSeparator = getLineEndingStyle().asRawString();
        String[] lines = content.split(lineSeparator);
        StringBuilder builder = new StringBuilder();
        for (String line : lines) {
            builder.append(getHeader());
            builder.append(line);
            builder.append(lineSeparator);
        }
        return builder.toString();
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isMarkdownComment() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public MarkdownComment asMarkdownComment() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<MarkdownComment> toMarkdownComment() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifMarkdownComment(Consumer<MarkdownComment> action) {
        action.accept(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public MarkdownComment clone() {
        return (MarkdownComment) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public MarkdownCommentMetaModel getMetaModel() {
        return JavaParserMetaModel.markdownCommentMetaModel;
    }
}
