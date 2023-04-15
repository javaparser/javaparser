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

package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.stmt.Statement;
import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.AfterEach;

import java.io.IOException;

import static com.github.javaparser.utils.TestUtils.assertEqualsString;
import static com.github.javaparser.utils.TestUtils.readResource;

public abstract class AbstractLexicalPreservingTest {

    protected CompilationUnit cu;
    protected Expression expression;
    protected Statement statement;
    
    @AfterAll
    public static void tearDown() {
    }
    
    @AfterEach
    public void reset() {
        StaticJavaParser.setConfiguration(new ParserConfiguration());
    }

    protected void considerCode(String code) {
        cu = LexicalPreservingPrinter.setup(StaticJavaParser.parse(code));
    }

    protected void considerExpression(String code) {
        expression = LexicalPreservingPrinter.setup(StaticJavaParser.parseExpression(code));
    }
    
    protected void considerStatement(String code) {
        statement = LexicalPreservingPrinter.setup(StaticJavaParser.parseStatement(code));
    }

    protected void considerVariableDeclaration(String code) {
        expression = LexicalPreservingPrinter.setup(StaticJavaParser.parseVariableDeclarationExpr(code));
    }

    protected String considerExample(String resourceName) throws IOException {
        String code = readExample(resourceName);
        considerCode(code);
        return code;
    }

    protected String readExample(String resourceName) throws IOException {
        return readResource("com/github/javaparser/lexical_preservation_samples/" + resourceName + ".java.txt");
    }

    protected void assertTransformed(String exampleName, Node node) throws IOException {
        String expectedCode = readExample(exampleName + "_expected");
        String actualCode = LexicalPreservingPrinter.print(node);

        // Note that we explicitly care about line endings when handling lexical preservation.
        assertEqualsString(expectedCode, actualCode);
    }

    protected void assertUnchanged(String exampleName) throws IOException {
        String expectedCode = considerExample(exampleName + "_original");
        String actualCode = LexicalPreservingPrinter.print(cu != null ? cu : expression);

        // Note that we explicitly care about line endings when handling lexical preservation.
        assertEqualsString(expectedCode, actualCode);
    }

    protected void assertTransformedToString(String expectedPartialCode, Node node) {
        String actualCode = LexicalPreservingPrinter.print(node);

        // Note that we explicitly care about line endings when handling lexical preservation.
        assertEqualsString(expectedPartialCode, actualCode);
    }

}
