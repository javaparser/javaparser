/*
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

package com.github.javaparser.printer.lexicalpreservation;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.util.stream.Stream;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;
import org.junit.jupiter.params.provider.ValueSource;

class Issue4074Test extends AbstractLexicalPreservingTest {

    @ParameterizedTest
    @ValueSource(strings = {"\n", "\r\n"})
    void removingLastImportPreservesBlankLineBeforeClass(String eol) {
        considerCode("import a;" + eol + "import b;" + eol + eol + "class X{}");

        cu.getImports().remove(1);

        assertEquals("import a;" + eol + eol + "class X{}", LexicalPreservingPrinter.print(cu));
    }

    @ParameterizedTest
    @MethodSource("importPositions")
    void removingImportPreservesRemainingImportsAndBlankLine(String eol, int index) {
        String[] imports = {"import a;", "import b;", "import c;"};
        considerCode(String.join(eol, imports) + eol + eol + "class X{}");

        cu.getImports().remove(index);

        String expected = imports[(index == 0) ? 1 : 0] + eol + imports[(index == 2) ? 1 : 2] + eol + eol + "class X{}";
        assertEquals(expected, LexicalPreservingPrinter.print(cu));
    }

    private static Stream<Arguments> importPositions() {
        return Stream.of("\n", "\r\n").flatMap(eol -> Stream.of(0, 1, 2).map(index -> Arguments.of(eol, index)));
    }

    @ParameterizedTest
    @MethodSource("classSeparators")
    void removingLastImportPreservesOriginalClassSeparator(String eol, String separator) {
        considerCode("import a;" + eol + "import b;" + separator + "class X{}");

        cu.getImports().remove(1);

        assertEquals("import a;" + separator + "class X{}", LexicalPreservingPrinter.print(cu));
    }

    private static Stream<Arguments> classSeparators() {
        return Stream.of("\n", "\r\n")
                .flatMap(eol -> Stream.of(eol, eol + eol + eol).map(separator -> Arguments.of(eol, separator)));
    }

    @ParameterizedTest
    @ValueSource(strings = {"\n", "\r\n"})
    void removingLastImportPreservesWhitespaceOnBlankLine(String eol) {
        String separator = eol + " \t" + eol;
        considerCode("import a;" + eol + "import b;" + separator + "class X{}");

        cu.getImports().remove(1);

        assertEquals("import a;" + separator + "class X{}", LexicalPreservingPrinter.print(cu));
    }

    @ParameterizedTest
    @ValueSource(strings = {"\n", "\r\n"})
    void removingLastImportsSuccessivelyPreservesBlankLine(String eol) {
        considerCode("import a;" + eol + "import b;" + eol + "import c;" + eol + eol + "class X{}");

        cu.getImports().remove(2);
        cu.getImports().remove(1);

        assertEquals("import a;" + eol + eol + "class X{}", LexicalPreservingPrinter.print(cu));
    }

    @ParameterizedTest
    @ValueSource(strings = {"\n", "\r\n"})
    void removingLastImportPreservesClassCommentAndBlankLine(String eol) {
        String classWithComment = "/** Class documentation. */" + eol + "class X{}";
        considerCode("import a;" + eol + "import b;" + eol + eol + classWithComment);

        cu.getImports().remove(1);

        assertEquals("import a;" + eol + eol + classWithComment, LexicalPreservingPrinter.print(cu));
    }

    @ParameterizedTest
    @ValueSource(strings = {"\n", "\r\n"})
    void removingIndentedLastImportPreservesBlankLine(String eol) {
        considerCode("import a;" + eol + " \timport b;" + eol + eol + "class X{}");

        cu.getImports().remove(1);

        assertEquals("import a;" + eol + eol + "class X{}", LexicalPreservingPrinter.print(cu));
    }
}
