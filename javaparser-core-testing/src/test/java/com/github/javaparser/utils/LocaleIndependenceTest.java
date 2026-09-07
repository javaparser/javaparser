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

package com.github.javaparser.utils;

import static com.github.javaparser.StaticJavaParser.parse;
import static org.junit.jupiter.api.Assertions.assertEquals;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.printer.lexicalpreservation.LexicalPreservingPrinter;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import java.util.Locale;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

/**
 * JavaParser transforms Java identifiers and keywords with {@code toLowerCase()} /
 * {@code toUpperCase()} in a number of places. Those overloads use the default locale, and in a
 * Turkish locale {@code 'I'} lower-cases to {@code 'ı'} (dotless) and {@code 'i'} upper-cases to
 * {@code 'İ'} (dotted). Since these strings are Java source, not human-readable text, the
 * conversions must be locale-independent.
 *
 * <p>See issue 3018.
 */
class LocaleIndependenceTest {

    private static final Locale TURKISH = Locale.forLanguageTag("tr-TR");

    private Locale previousDefault;

    @BeforeEach
    void setTurkishLocale() {
        previousDefault = Locale.getDefault();
        Locale.setDefault(TURKISH);
    }

    @AfterEach
    void restoreLocale() {
        Locale.setDefault(previousDefault);
    }

    @Test
    void utilsCaseConversionsAreLocaleIndependent() {
        assertEquals("Int", Utils.capitalize("int"));
        assertEquals("int", Utils.decapitalize("Int"));
        assertEquals("isInterface", Utils.screamingToCamelCase("IS_INTERFACE"));
        assertEquals("IS_INTERFACE", Utils.camelCaseToScreaming("isInterface"));
    }

    @Test
    void observablePropertyNamesAreLocaleIndependent() {
        // camelCaseName() feeds the reflective getter lookup in ObservableProperty#getRawValue,
        // so a mangled name makes the property unreadable. 43 of the 104 constants contain an 'I'.
        assertEquals("annotations", ObservableProperty.ANNOTATIONS.camelCaseName());
        assertEquals("interface", ObservableProperty.INTERFACE.camelCaseName());
        assertEquals(ObservableProperty.ANNOTATIONS, ObservableProperty.fromCamelCaseName("annotations"));
    }

    @Test
    void observablePropertyValuesAreReadable() {
        CompilationUnit cu = parse("class A { }");
        assertEquals("[]", String.valueOf(ObservableProperty.ANNOTATIONS.getRawValue(cu.getType(0))));
    }

    @Test
    void lexicalPreservingPrinterWorksInAnyLocale() {
        CompilationUnit cu = parse("class A { void f(){} }");
        LexicalPreservingPrinter.setup(cu);
        cu.getType(0)
                .asClassOrInterfaceDeclaration()
                .getMethods()
                .get(0)
                .setModifiers(Modifier.Keyword.PUBLIC, Modifier.Keyword.STATIC);
        assertEquals("class A { public static void f(){} }", LexicalPreservingPrinter.print(cu));
    }

    @Test
    void generatedAccessorNamesAreLocaleIndependent() {
        CompilationUnit cu = parse("class A { int id; }");
        FieldDeclaration field =
                cu.getType(0).asClassOrInterfaceDeclaration().getFields().get(0);
        assertEquals("getId", field.createGetter().getNameAsString());
        assertEquals("setId", field.createSetter().getNameAsString());
    }

    @Test
    void resolvedPrimitiveTypeLookupIsLocaleIndependent() {
        assertEquals(ResolvedPrimitiveType.INT, ResolvedPrimitiveType.byName("INT"));
        assertEquals(ResolvedPrimitiveType.INT, ResolvedPrimitiveType.byName("int"));
    }
}
