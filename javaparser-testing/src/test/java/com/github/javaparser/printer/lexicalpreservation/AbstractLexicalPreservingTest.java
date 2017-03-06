/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
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

import com.github.javaparser.ParseResult;
import com.github.javaparser.ParseStart;
import com.github.javaparser.Providers;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.utils.Pair;
import org.junit.Before;

import java.io.IOException;

import static com.github.javaparser.utils.TestUtils.readResource;
import static org.junit.Assert.assertEquals;

public abstract class AbstractLexicalPreservingTest {

    protected LexicalPreservingPrinter lpp;
    protected CompilationUnit cu;
    protected Expression expression;

    @Before
    public void setup() {
        lpp = null;
        cu = null;
    }

    protected void considerCode(String code) {
        Pair<ParseResult<CompilationUnit>, LexicalPreservingPrinter> res = LexicalPreservingPrinter.setup(
                ParseStart.COMPILATION_UNIT, Providers.provider(code));
        cu = res.a.getResult().get();
        lpp = res.b;
    }

    protected void considerExpression(String code) {
        Pair<ParseResult<Expression>, LexicalPreservingPrinter> res = LexicalPreservingPrinter.setup(
                ParseStart.EXPRESSION, Providers.provider(code));
        expression = res.a.getResult().get();
        lpp = res.b;
    }

    protected String considerExample(String resourceName) throws IOException {
        String code = readExample(resourceName);
        considerCode(code);
        return code;
    }

    protected String readExample(String resourceName) throws IOException {
        return readResource("/com/github/javaparser/lexical_preservation_samples/" + resourceName + ".java.txt");
    }

    protected void assertTransformed(String exampleName, Node node) throws IOException {
        String expectedCode = readExample(exampleName + "_expected");
        String actualCode = lpp.print(node);
        assertEquals(expectedCode, actualCode);
    }

    protected void assertUnchanged(String exampleName) throws IOException {
        String code = considerExample(exampleName + "_original");
        assertEquals(code, lpp.print(cu != null ? cu : expression));
    }

    protected void assertTransformedToString(String expectedPartialCode, Node node) throws IOException {
        String actualCode = lpp.print(node);
        assertEquals(expectedPartialCode, actualCode);
    }

}
