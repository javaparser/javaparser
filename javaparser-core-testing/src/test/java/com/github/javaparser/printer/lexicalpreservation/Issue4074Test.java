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

/*
 * Removing an element of a list must remove the element together with its own separator and preserve the
 * whitespace that follows the list, whatever the number of line breaks the source actually contains.
 * The CSM of the imports ends with two line breaks (a blank line before the type), so the source can have fewer
 * or more line breaks than the CSM expects.
 */
class Issue4074Test extends AbstractLexicalPreservingTest {

    @ParameterizedTest
    @ValueSource(strings = {"\n", "\r\n"})
    void removingLastImportKeepsBlankLineBeforeType(String eol) {
        considerCode(
                "import java.util.List;" + eol + "import java.util.Map;" + eol + eol + "public class Foo {}" + eol);

        cu.getImports().remove(1);

        assertEquals(
                "import java.util.List;" + eol + eol + "public class Foo {}" + eol, LexicalPreservingPrinter.print(cu));
    }

    /*
     * The separator between the imports and the type is kept as it is: no line break, a blank line, several blank
     * lines, or a blank line containing spaces.
     */
    @ParameterizedTest
    @MethodSource("separatorsBeforeType")
    void removingLastImportKeepsSeparatorBeforeType(String eol, String separator) {
        considerCode("import a;" + eol + "import b;" + separator + "class X {}");

        cu.getImports().remove(1);

        assertEquals("import a;" + separator + "class X {}", LexicalPreservingPrinter.print(cu));
    }

    static Stream<Arguments> separatorsBeforeType() {
        return Stream.of("\n", "\r\n").flatMap(eol -> Stream.of(eol, eol + eol, eol + eol + eol, eol + "  \t" + eol)
                .map(separator -> Arguments.of(eol, separator)));
    }

    @ParameterizedTest
    @MethodSource("removedImportIndexes")
    void removingAnyImportKeepsOtherImportsAndBlankLine(String eol, int removedIndex) {
        String[] imports = {"import a;", "import b;", "import c;"};
        considerCode(String.join(eol, imports) + eol + eol + "class X {}");

        cu.getImports().remove(removedIndex);

        StringBuilder expected = new StringBuilder();
        for (int i = 0; i < imports.length; i++) {
            if (i != removedIndex) {
                expected.append(imports[i]).append(eol);
            }
        }
        expected.append(eol).append("class X {}");
        assertEquals(expected.toString(), LexicalPreservingPrinter.print(cu));
    }

    static Stream<Arguments> removedImportIndexes() {
        return Stream.of("\n", "\r\n").flatMap(eol -> Stream.of(0, 1, 2).map(index -> Arguments.of(eol, index)));
    }

    @ParameterizedTest
    @ValueSource(strings = {"\n", "\r\n"})
    void removingLastImportsOneAfterTheOtherKeepsBlankLine(String eol) {
        considerCode("import a;" + eol + "import b;" + eol + "import c;" + eol + eol + "class X {}");

        cu.getImports().remove(2);
        cu.getImports().remove(1);

        assertEquals("import a;" + eol + eol + "class X {}", LexicalPreservingPrinter.print(cu));
    }

    @ParameterizedTest
    @ValueSource(strings = {"\n", "\r\n"})
    void removingLastImportKeepsPackageAndTypeComment(String eol) {
        considerCode("package p;" + eol + eol + "import a;" + eol + "import b;" + eol + eol + "/** Doc. */" + eol
                + "class X {}");

        cu.getImports().remove(1);

        assertEquals(
                "package p;" + eol + eol + "import a;" + eol + eol + "/** Doc. */" + eol + "class X {}",
                LexicalPreservingPrinter.print(cu));
    }

    @ParameterizedTest
    @ValueSource(strings = {"\n", "\r\n"})
    void removingLastTypeRemovesItsSeparator(String eol) {
        considerCode("class A {}" + eol + eol + "class B {}" + eol);

        cu.getTypes().remove(1);

        assertEquals("class A {}" + eol, LexicalPreservingPrinter.print(cu));
    }
}
