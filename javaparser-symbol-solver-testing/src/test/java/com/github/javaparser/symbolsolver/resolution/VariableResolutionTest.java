/*
 * Copyright (C) 2013-2024 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.resolution;

import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.util.List;
import org.junit.jupiter.api.Test;

public class VariableResolutionTest extends AbstractResolutionTest {

    @Test
    void variableResolutionNoBlockStmt() {
        // Test without nested block statement

        CompilationUnit cu = parseSample("VariableResolutionInVariousScopes");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "VariableResolutionInVariousScopes");

        MethodDeclaration method = Navigator.demandMethod(clazz, "noBlock");
        MethodCallExpr callExpr = method.findFirst(MethodCallExpr.class).get();
        MethodUsage methodUsage =
                JavaParserFacade.get(new ReflectionTypeSolver()).solveMethodAsUsage(callExpr);

        assertTrue(methodUsage.declaringType().getQualifiedName().equals("java.lang.String"));
    }

    @Test
    void variableResolutionWithBlockStmt() {
        // Test without nested block statement

        CompilationUnit cu = parseSample("VariableResolutionInVariousScopes");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "VariableResolutionInVariousScopes");

        MethodDeclaration method = Navigator.demandMethod(clazz, "withBlock");
        MethodCallExpr callExpr = method.findFirst(MethodCallExpr.class).get();
        MethodUsage methodUsage =
                JavaParserFacade.get(new ReflectionTypeSolver()).solveMethodAsUsage(callExpr);

        assertTrue(methodUsage.declaringType().getQualifiedName().equals("java.lang.String"));
    }

    @Test
    public void symbolAsValueInForStmtTest() {
        String code = "public class Board {\n" + "\n"
                + "    class Field {\n"
                + "        private final Board board;\n"
                + "        private final int x;\n"
                + "        private final int y;\n"
                + "\n"
                + "        public Field(Board board, int x, int y) {\n"
                + "            this.board = board;\n"
                + "            this.x = x;\n"
                + "            this.y = y;\n"
                + "        }\n"
                + "    }\n"
                + "\n"
                + "    /**\n"
                + "     * Edge size of the Sudoku board.\n"
                + "     */\n"
                + "    public static final int SIZE = 9;\n"
                + "    private final Field[] board = new Field[SIZE * SIZE];\n"
                + "\n"
                + "    /**\n"
                + "     * Creates a Sudoku board with all of its fields being empty.\n"
                + "     */\n"
                + "    public Board() {\n"
                + "        for (int x = 0; x < SIZE; x++)\n"
                + "            for (int y = 0; y < SIZE; y++)\n"
                + "                board[SIZE * y + x] = new Field(this, x, y);\n"
                + "    }\n"
                + "}";
        StaticJavaParser.getParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        CompilationUnit cu = StaticJavaParser.parse(code);

        final List<ObjectCreationExpr> objectCreationExprs = cu.findAll(ObjectCreationExpr.class);

        for (ObjectCreationExpr objectCreationExpr : objectCreationExprs) {
            System.err.println(objectCreationExpr.toString());
            for (Expression e : objectCreationExpr.getArguments()) {
                System.err.println(e.toString());
                if (e.isNameExpr()) {
                    NameExpr ne = e.asNameExpr();
                    final ResolvedValueDeclaration resolve = ne.resolve();
                    System.err.println(resolve);
                    System.err.println(resolve.getType().describe());
                }
            }
            final ResolvedConstructorDeclaration resolve = objectCreationExpr.resolve();
            System.err.println(resolve.getQualifiedName());
            System.err.println(resolve.getQualifiedSignature());
        }
    }
}
