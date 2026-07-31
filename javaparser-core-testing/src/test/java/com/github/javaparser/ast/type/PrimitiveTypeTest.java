/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
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

package com.github.javaparser.ast.type;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.StaticJavaParser;
import java.util.Locale;
import java.util.Optional;
import org.junit.jupiter.api.Test;

class PrimitiveTypeTest {

    /**
     * https://github.com/javaparser/javaparser/issues/3018
     * <p>
     * Code generation must not depend on the JVM's default locale. The no-arg
     * {@code String.toLowerCase()} folds letters using the default locale's case-folding rules;
     * under a Turkish ("tr") default locale, capital "I" lower-cases to dotless "ı" (U+0131) instead
     * of ASCII "i", so {@code "INT".toLowerCase()} yields "ınt" instead of "int". That corrupted the
     * printed primitive-type keyword and also broke {@code byTypeName("int")} lookups. Both call
     * sites must pin {@code Locale.ROOT} so behavior is identical regardless of the JVM's default
     * locale.
     */
    @Test
    void issue3018() {
        Locale originalLocale = Locale.getDefault();
        try {
            Locale.setDefault(Locale.forLanguageTag("tr"));

            String printed =
                    StaticJavaParser.parse("class A { void f(int x) {} }").toString();
            assertTrue(
                    printed.contains("int"),
                    "expected printed output to contain the ASCII keyword \"int\": " + printed);
            // "ınt" (dotless-i) is the Turkish corruption of the "int" keyword.
            assertFalse(
                    printed.contains("ınt"),
                    "printed output must not contain the Turkish dotless-i corruption \"ınt\": " + printed);

            Optional<PrimitiveType.Primitive> resolved = PrimitiveType.Primitive.byTypeName("int");
            assertTrue(resolved.isPresent(), "byTypeName(\"int\") must still resolve under a Turkish default locale");
            assertEquals(PrimitiveType.Primitive.INT, resolved.get());
        } finally {
            Locale.setDefault(originalLocale);
        }
    }
}
