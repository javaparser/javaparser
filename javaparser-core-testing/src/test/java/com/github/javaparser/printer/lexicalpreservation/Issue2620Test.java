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

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.utils.LineSeparator;
import org.junit.jupiter.api.Test;

import java.util.Optional;

import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

public class Issue2620Test extends AbstractLexicalPreservingTest {

    @Test
    public void testWithCr() {
        doTest(LineSeparator.CR);
    }

    @Test
    public void testWithLf() {
        doTest(LineSeparator.LF);
    }

    @Test
    public void testWithCrLf() {
        doTest(LineSeparator.CRLF);
    }


    /*
     * This test case must prevent an UnsupportedOperation Removed throwed by LexicalPreservation when we try to replace an expression
     */
    public void doTest(LineSeparator eol) {

        considerCode("" +
                "    public class Foo { //comment" + eol +
                "        private String a;" + eol +
                "        private String b;" + eol +
                "        private String c;" + eol +
                "        private String d;" + eol +
                "    }");

        // Note: Expect the platform's EOL character when printing
        // FIXME: Indentation is bad here.
        String expected = "" +
                "    public class Foo { //comment" + eol +
                "        private String newField;" + eol +
                "        " + eol +
                "        private String a;" + eol +
                "        private String b;" + eol +
                "        private String c;" + eol +
                "        private String d;" + eol +
                "    }";


        // create a new field declaration
        VariableDeclarator variable = new VariableDeclarator(new ClassOrInterfaceType("String"), "newField");
        FieldDeclaration fd = new FieldDeclaration(new NodeList(Modifier.privateModifier()), variable);
        Optional<ClassOrInterfaceDeclaration> cd = cu.findFirst(ClassOrInterfaceDeclaration.class);

        // add the new variable
        cd.get().getMembers().addFirst(fd);

        // should be printed like this
//        System.out.println("\n\nOriginal:\n" + original);
//        System.out.println("\n\nExpected:\n" + expected);

        // but the result is
        final String actual = LexicalPreservingPrinter.print(cu);
//        System.out.println("\n\nActual:\n" + actual);

        LineSeparator detectedLineSeparator = LineSeparator.detect(actual);

        assertFalse(detectedLineSeparator.equals(LineSeparator.MIXED));
        assertEquals(eol.asEscapedString(), detectedLineSeparator.asEscapedString());

        assertEquals(normaliseNewlines(expected), normaliseNewlines(actual));

        // Commented out until #2661 is fixed (re: EOL characters of injected code)
        assertEqualsStringIgnoringEol(escapeNewlines(expected), escapeNewlines(actual));
        assertEquals(expected, actual, "Failed due to EOL differences.");
    }

    private String escapeNewlines(String input) {
        return input
                .replaceAll("\\r", "\\\\r")
                .replaceAll("\\n", "\\\\n");
    }

    private String normaliseNewlines(String input) {
        return input.replaceAll("\\r\\n|\\r|\\n", "\\\\n");
    }
}
