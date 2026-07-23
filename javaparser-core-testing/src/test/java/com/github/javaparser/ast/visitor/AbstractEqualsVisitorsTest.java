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

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import java.util.function.BiFunction;

public abstract class AbstractEqualsVisitorsTest {
    protected CompilationUnit nodeLeft;
    protected CompilationUnit nodeRight;

    private CompilationUnit parse(String code) {
        ParserConfiguration configuration = new ParserConfiguration();
        configuration.setLanguageLevel(ParserConfiguration.LanguageLevel.BLEEDING_EDGE);
        return new JavaParser(configuration).parse(code).getResult().get();
    }

    private CompilationUnit cloneNode(CompilationUnit node) {
        return node.clone();
    }

    protected void parseAndClone(String code) {
        nodeLeft = parse(code);
        nodeRight = cloneNode(nodeLeft);
    }

    enum Strategy {
        STANDARD(EqualsVisitor::equals, true),
        NO_COMMENT(NoCommentEqualsVisitor::equals, false);

        private final BiFunction<Node, Node, Boolean> equals;
        private final boolean commentMatters;

        Strategy(BiFunction<Node, Node, Boolean> equals, boolean commentMatters) {
            this.equals = equals;
            this.commentMatters = commentMatters;
        }

        boolean areEqual(Node leftNode, Node rightNode) {
            return equals.apply(leftNode, rightNode);
        }

        boolean expectedResultOnDifferentComments() {
            return !commentMatters;
        }
    }
}
