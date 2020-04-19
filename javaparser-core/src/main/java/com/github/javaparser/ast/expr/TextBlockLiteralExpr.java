/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2020 The JavaParser Team.
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
package com.github.javaparser.ast.expr;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.TextBlockLiteralExprMetaModel;
import com.github.javaparser.utils.Pair;
import java.util.Arrays;
import java.util.Optional;
import java.util.function.Consumer;
import java.util.stream.Stream;
import static com.github.javaparser.utils.StringEscapeUtils.unescapeJavaTextBlock;
import static java.util.stream.Collectors.joining;
import static java.util.stream.IntStream.range;

/**
 * <h1>A text block</h1>
 * <h2>Java 13-</h2>
 * A text block is a multi-line string. It was introduced in JEP 355.
 * The content of "value" is byte-for-byte exactly what is in the source code.
 */
public class TextBlockLiteralExpr extends LiteralStringValueExpr {

    public TextBlockLiteralExpr() {
        this(null, "empty");
    }

    /**
     * Creates a text block literal expression from given string.
     *
     * @param value the value of the literal
     */
    @AllFieldsConstructor
    public TextBlockLiteralExpr(final String value) {
        this(null, value);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public TextBlockLiteralExpr(TokenRange tokenRange, String value) {
        super(tokenRange, value);
        customInitialization();
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
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isTextBlockLiteralExpr() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public TextBlockLiteralExpr asTextBlockLiteralExpr() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<TextBlockLiteralExpr> toTextBlockLiteralExpr() {
        return Optional.of(this);
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifTextBlockLiteralExpr(Consumer<TextBlockLiteralExpr> action) {
        action.accept(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public TextBlockLiteralExpr clone() {
        return (TextBlockLiteralExpr) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public TextBlockLiteralExprMetaModel getMetaModel() {
        return JavaParserMetaModel.textBlockLiteralExprMetaModel;
    }

    /**
     * Most of the algorithm for stripIndent, stopping just before concatenating all the lines into a single string.
     * Useful for tools.
     */
    public Stream<String> stripIndentOfLines() {
        /* Split the content of the text block at every LF, producing a list of individual lines. 
        Note that any line in the content which was just an LF will become an empty line in the list of individual lines. */
        String[] rawLines = getValue().split("\\R", -1);
        /* Add all non-blank lines from the list of individual lines into a set of determining lines. 
        (Blank lines -- lines that are empty or are composed wholly of white space -- have no visible influence on the indentation. 
        Excluding blank lines from the set of determining lines avoids throwing off step 4 of the algorithm.) */
        /* If the last line in the list of individual lines (i.e., the line with the closing delimiter) is blank, then add it to the set of determining lines. 
        (The indentation of the closing delimiter should influence the indentation of the content as a whole -- a "significant trailing line" policy.) */
        /* Compute the common white space prefix of the set of determining lines, by counting the number of leading white space characters on each line and taking the minimum count. */
        int commonWhiteSpacePrefixSize = range(0, rawLines.length).mapToObj(nr -> new Pair<>(nr, rawLines[nr])).filter(l -> !emptyOrWhitespace(l.b) || isLastLine(rawLines, l.a)).map(l -> indentSize(l.b)).min(Integer::compare).orElse(0);
        /* Remove the common white space prefix from each non-blank line in the list of individual lines. */
        /* Remove all trailing white space from all lines in the modified list of individual lines from step 5. 
        This step collapses wholly-whitespace lines in the modified list so that they are empty, but does not discard them. */
        return Arrays.stream(rawLines).map(l -> l.substring(commonWhiteSpacePrefixSize)).map(this::trimTrailing);
    }

    /**
     * @return The algorithm from String::stripIndent in JDK 13.
     */
    public String stripIndent() {
        /* Construct the result string by joining all the lines in the modified list of individual lines from step 6, using LF as the separator between lines. 
        If the final line in the list from step 6 is empty, then the joining LF from the previous line will be the last character in the result string. */
        return stripIndentOfLines().collect(joining("\n"));
    }

    /**
     * @return The algorithm from String::translateEscapes in JDK 13.
     */
    public String translateEscapes() {
        return unescapeJavaTextBlock(stripIndent());
    }

    /**
     * @return the final string value of this text block after all processing.
     */
    public String asString() {
        return translateEscapes();
    }

    /**
     * @return is the line with index lineNr the last line in rawLines?
     */
    private boolean isLastLine(String[] rawLines, Integer lineNr) {
        return lineNr == rawLines.length - 1;
    }

    /**
     * @return is this string empty or filled only with whitespace?
     */
    private boolean emptyOrWhitespace(String rawLine) {
        return rawLine.trim().isEmpty();
    }

    /**
     * @return the amount of leading whitespaces.
     */
    private int indentSize(String s) {
        String content = s.trim();
        if (content.isEmpty()) {
            return s.length();
        }
        return s.indexOf(content);
    }

    /**
     * Can be replaced when moving to JDK 11
     */
    private String trimTrailing(String source) {
        int pos = source.length() - 1;
        while ((pos >= 0) && Character.isWhitespace(source.charAt(pos))) {
            pos--;
        }
        pos++;
        return (pos < source.length()) ? source.substring(0, pos) : source;
    }
}
