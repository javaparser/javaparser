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
package com.github.javaparser.ast.validator;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.StringLiteralExpr;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import org.junit.jupiter.api.Test;

class TreeVisitorValidatorTest {

    /**
     * A deeply nested expression (such as a long string concatenation) used to make {@link TreeVisitorValidator}
     * recurse once per tree level, overflowing the call stack and causing a {@link StackOverflowError}. See <a
     * href="https://github.com/javaparser/javaparser/issues/4439">issue 4439</a>.
     */
    @Test
    void deeplyNestedTreeIsVisitedWithoutStackOverflow() {
        int depth = 100_000;

        // Build "a" + "a" + "a" + ... which nests BinaryExpr nodes `depth` levels deep.
        Expression expression = new StringLiteralExpr("a");
        for (int i = 0; i < depth; i++) {
            expression = new BinaryExpr(expression, new StringLiteralExpr("a"), BinaryExpr.Operator.PLUS);
        }

        AtomicInteger visited = new AtomicInteger();
        TreeVisitorValidator validator = new TreeVisitorValidator((node, reporter) -> visited.incrementAndGet());

        Expression deepExpression = expression;
        assertDoesNotThrow(() -> validator.accept(deepExpression, new ProblemReporter(problem -> {})));
        assertEquals(2 * depth + 1, visited.get());
    }

    /**
     * Tests that the TreeVisitorValidator visits nodes pre-order traversal: the default order of any visitor.
     */
    @Test
    void visitorFollowsPreOrderTraversal() {
        // Create a small tree: (("a" + "b") + "c")
        // Structure:
        //      +
        //     / \
        //    +   "c"
        //   / \
        // "a" "b"
        StringLiteralExpr a = new StringLiteralExpr("a");
        StringLiteralExpr b = new StringLiteralExpr("b");
        BinaryExpr ab = new BinaryExpr(a, b, BinaryExpr.Operator.PLUS);
        StringLiteralExpr c = new StringLiteralExpr("c");
        BinaryExpr abc = new BinaryExpr(ab, c, BinaryExpr.Operator.PLUS);

        List<Node> visitedNodes = new ArrayList<>();
        TreeVisitorValidator validator = new TreeVisitorValidator((node, reporter) -> visitedNodes.add(node));
        validator.accept(abc, new ProblemReporter(problem -> {}));

        // Pre-order expectation: parent, left child, right child.
        assertEquals(Arrays.asList(abc, ab, a, b, c), visitedNodes);
    }
}
