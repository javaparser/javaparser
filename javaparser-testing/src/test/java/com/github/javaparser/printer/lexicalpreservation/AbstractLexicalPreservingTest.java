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
import com.github.javaparser.ast.body.AnnotationMemberDeclaration;
import com.github.javaparser.utils.Pair;
import org.junit.Before;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;

import static org.junit.Assert.assertEquals;

public abstract class AbstractLexicalPreservingTest {

    protected LexicalPreservingPrinter lpp;
    protected CompilationUnit cu;

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

    protected String considerExample(String resourceName) throws IOException {
        String code = readExample(resourceName);
        considerCode(code);
        return code;
    }

    protected String readExample(String resourceName) throws IOException {
        InputStream is = this.getClass().getResourceAsStream("/com/github/javaparser/lexical_preservation_samples/" + resourceName + ".java.txt");
        if (is == null) {
            throw new IllegalArgumentException("Example not found: " + resourceName);
        }
        return read(is);
    }

    protected String read(InputStream inputStream) throws IOException {
        ByteArrayOutputStream result = new ByteArrayOutputStream();
        byte[] buffer = new byte[1024];
        int length;
        while ((length = inputStream.read(buffer)) != -1) {
            result.write(buffer, 0, length);
        }
        return result.toString("UTF-8");
    }

    protected void assertTransformed(String exampleName, CompilationUnit cu) throws IOException {
        String expectedCode = readExample(exampleName + "_expected");
        String actualCode = lpp.print(cu);
        assertEquals(expectedCode, actualCode);
    }

    protected void assertUnchanged(String exampleName) throws IOException {
        String code = considerExample(exampleName + "_original");
        assertEquals(code, lpp.print(cu));
    }

    protected void assertTransformedToString(String expectedPartialCode, Node node) throws IOException {
        String actualCode = lpp.print(node);
        assertEquals(expectedPartialCode, actualCode);
    }

}
