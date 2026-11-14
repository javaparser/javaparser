/*
 * Copyright (C) 2013-2026 The JavaParser Team.
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

import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;

import com.github.javaparser.ParserConfiguration.LanguageLevel;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

/**
 * Regression tests for issue #4801: removing the {@code permits} clause (and optionally the {@code sealed}
 * modifier) of a type with the {@link LexicalPreservingPrinter} must not throw and must keep the rest of the
 * source untouched.
 */
class Issue4801Test extends AbstractLexicalPreservingTest {

    @BeforeEach
    void setLanguageLevel() {
        parser.getParserConfiguration().setLanguageLevel(LanguageLevel.JAVA_17);
    }

    private void removePermits() {
        cu.findAll(ClassOrInterfaceDeclaration.class).forEach(d -> d.setPermittedTypes(new NodeList<>()));
    }

    @Test
    void removePermitsFromSealedClass() {
        considerCode("public sealed class Foo permits Bar, Baz {}");

        removePermits();

        assertEqualsStringIgnoringEol("public sealed class Foo {}", LexicalPreservingPrinter.print(cu));
    }

    @Test
    void removePermitsKeepsTypeParametersExtendsAndImplements() {
        considerCode("public sealed class Foo<T> extends Base<T> implements I, J permits Bar, Baz {\n  int x;\n}");

        removePermits();

        assertEqualsStringIgnoringEol(
                "public sealed class Foo<T> extends Base<T> implements I, J {\n  int x;\n}",
                LexicalPreservingPrinter.print(cu));
    }

    @Test
    void downgradeSealedClassToNormalClass() {
        considerCode("public sealed class Foo extends Base implements I permits Bar, Baz {\n  int x;\n}");

        cu.findAll(ClassOrInterfaceDeclaration.class).forEach(d -> {
            d.setPermittedTypes(new NodeList<>());
            d.removeModifier(Modifier.Keyword.SEALED);
        });

        assertEqualsStringIgnoringEol(
                "public class Foo extends Base implements I {\n  int x;\n}", LexicalPreservingPrinter.print(cu));
    }

    @Test
    void downgradeSealedInterfaceRemovingModifierFirst() {
        considerCode("sealed interface Foo extends X permits Bar {}");

        cu.findAll(ClassOrInterfaceDeclaration.class).forEach(d -> {
            d.removeModifier(Modifier.Keyword.SEALED);
            d.setPermittedTypes(new NodeList<>());
        });

        assertEqualsStringIgnoringEol("interface Foo extends X {}", LexicalPreservingPrinter.print(cu));
    }
}
