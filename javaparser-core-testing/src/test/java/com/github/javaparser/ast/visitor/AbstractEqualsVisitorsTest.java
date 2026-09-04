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

import static com.github.javaparser.StaticJavaParser.newParserAdapter;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;
import static org.junit.jupiter.api.Assertions.assertFalse;

import com.github.javaparser.JavaParserAdapter;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.comments.LineComment;
import java.util.function.BiFunction;
import java.util.function.Consumer;
import java.util.function.Supplier;

public abstract class AbstractEqualsVisitorsTest {
    protected CompilationUnit nodeLeft;
    protected CompilationUnit nodeRight;

    private static final JavaParserAdapter PARSER = newParserAdapter(
            new ParserConfiguration().setLanguageLevel(ParserConfiguration.LanguageLevel.BLEEDING_EDGE));

    protected void parseAndClone(String code) {
        nodeLeft = PARSER.parse(code);
        nodeRight = nodeLeft.clone();
    }

    protected void assertCommentChangeHandled(String code, Supplier<? extends Node> nodeExtractor, Strategy strategy) {
        parseAndClone(code);
        nodeExtractor.get().setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    protected <T extends Node> void assertNotEqualAfterMutation(
            String code, Supplier<T> nodeExtractor, Consumer<T> mutation, Strategy strategy) {
        parseAndClone(code);
        mutation.accept(nodeExtractor.get());
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    enum Strategy {
        STANDARD(EqualsVisitor::equals, false),
        NO_COMMENT(NoCommentEqualsVisitor::equals, true);

        private final BiFunction<Node, Node, Boolean> equals;
        private final boolean expectedResultOnDifferentComments;

        Strategy(BiFunction<Node, Node, Boolean> equals, boolean expectedResultOnDifferentComments) {
            this.equals = equals;
            this.expectedResultOnDifferentComments = expectedResultOnDifferentComments;
        }

        boolean areEqual(Node leftNode, Node rightNode) {
            return equals.apply(leftNode, rightNode);
        }

        boolean expectedResultOnDifferentComments() {
            return expectedResultOnDifferentComments;
        }
    }
}
