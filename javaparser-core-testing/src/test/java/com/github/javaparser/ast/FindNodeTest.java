/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

package com.github.javaparser.ast;

import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.TryStmt;
import org.junit.jupiter.api.Test;

import java.util.function.Predicate;

import static com.github.javaparser.StaticJavaParser.parse;
import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Some tests for finding descendant and ancestor nodes.
 */
class FindNodeTest {
    @Test
    void testFindFirst() {
        CompilationUnit cu = parse(
                "class Foo {\n" +
                        "    void foo() {\n" +
                        "        try {\n" +
                        "        } catch (Exception e) {\n" +
                        "        } finally {\n" +
                        "            try {\n" +
                        "            } catch (Exception e) {\n" +
                        "                foo();\n" +
                        "            } finally {\n" +
                        "            }\n" +
                        "        }\n" +
                        "\n" +
                        "    }\n" +
                        "}\n");

        // find the method call expression foo()
        MethodCallExpr actual = cu.findFirst(MethodCallExpr.class).orElse(null);

        MethodCallExpr expected = cu.getType(0).getMember(0)
                .asMethodDeclaration().getBody().get().getStatement(0)
                .asTryStmt().getFinallyBlock().get().getStatement(0)
                .asTryStmt().getCatchClauses().get(0).getBody().getStatement(0)
                .asExpressionStmt().getExpression()
                .asMethodCallExpr();

        assertEquals(expected, actual);
    }

    @Test
    void testFindAncestralFinallyBlock() {
        CompilationUnit cu = parse(
                "class Foo {\n" +
                        "    void foo() {\n" +
                        "        try {\n" +
                        "        } catch (Exception e) {\n" +
                        "        } finally {\n" +
                        "            try {\n" +
                        "            } catch (Exception e) {\n" +
                        "                foo();\n" +
                        "            } finally {\n" +
                        "            }\n" +
                        "        }\n" +
                        "\n" +
                        "    }\n" +
                        "}\n");

        // find the method call expression foo()
        MethodCallExpr methodCallExpr = cu.findFirst(MethodCallExpr.class).orElse(null);

        // find the finally block that the method call expression foo() is in
        Predicate<BlockStmt> predicate = (bs) -> {
            if (bs.getParentNode().isPresent() && bs.getParentNode().get() instanceof TryStmt) {
                TryStmt ancestralTryStmt = (TryStmt) bs.getParentNode().get();
                return bs == ancestralTryStmt.getFinallyBlock().orElse(null);
            }
            return false;
        };
        BlockStmt actual = methodCallExpr.findAncestor(predicate, BlockStmt.class).orElse(null);

        BlockStmt expected = cu.getType(0).getMember(0)
                .asMethodDeclaration().getBody().get().getStatement(0)
                .asTryStmt().getFinallyBlock().get();

        assertEquals(expected, actual);
    }
}

