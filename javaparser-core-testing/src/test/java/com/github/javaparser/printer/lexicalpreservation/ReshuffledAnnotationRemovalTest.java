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

import com.github.javaparser.ast.body.MethodDeclaration;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

/*
 * Annotations and modifiers are printed through a CsmMix, so removing an annotation produces a reshuffled
 * difference. The annotation following the removed one must be kept in place, whatever the line separator.
 */
class ReshuffledAnnotationRemovalTest extends AbstractLexicalPreservingTest {

    private MethodDeclaration method() {
        return cu.findFirst(MethodDeclaration.class).get();
    }

    @ParameterizedTest
    @ValueSource(strings = {"\n", "\r\n"})
    void removingFirstAnnotationKeepsNextAnnotationAfterModifierInPlace(String eol) {
        considerCode("class X {" + eol + "    @A" + eol + "    public @B void method() {}" + eol + "}");

        method().getAnnotations().remove(0);

        assertEquals(
                "class X {" + eol + "    public @B void method() {}" + eol + "}", LexicalPreservingPrinter.print(cu));
    }

    @ParameterizedTest
    @ValueSource(strings = {"\n", "\r\n"})
    void removingFirstAnnotationKeepsCommentOfNextAnnotation(String eol) {
        considerCode("class X {" + eol + "    @Deprecated" + eol + "    // keep me" + eol
                + "    @SuppressWarnings(\"all\")" + eol + "    void method() {}" + eol + "}");

        method().getAnnotations().remove(0);

        assertEquals(
                "class X {" + eol + "    // keep me" + eol + "    @SuppressWarnings(\"all\")" + eol
                        + "    void method() {}" + eol + "}",
                LexicalPreservingPrinter.print(cu));
    }

    @ParameterizedTest
    @ValueSource(strings = {"\n", "\r\n"})
    void removingFirstAnnotationKeepsNextAnnotationLine(String eol) {
        considerCode("class X {" + eol + "    @Deprecated" + eol + "    @SuppressWarnings(\"all\")" + eol
                + "    void method() {}" + eol + "}");

        method().getAnnotations().remove(0);

        assertEquals(
                "class X {" + eol + "    @SuppressWarnings(\"all\")" + eol + "    void method() {}" + eol + "}",
                LexicalPreservingPrinter.print(cu));
    }

    @ParameterizedTest
    @ValueSource(strings = {"\n", "\r\n"})
    void removingAllAnnotationsKeepsMethodIndentation(String eol) {
        considerCode("class X {" + eol + "    @Deprecated" + eol + "    @SuppressWarnings(\"all\")" + eol
                + "    void method() {}" + eol + "}");

        method().getAnnotations().clear();

        assertEquals("class X {" + eol + "    void method() {}" + eol + "}", LexicalPreservingPrinter.print(cu));
    }
}
