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
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;

class ClassOrInterfaceTypeScopeTest extends AbstractLexicalPreservingTest {

    @BeforeEach
    void configureLexicalPreservation() {
        parser.getParserConfiguration().setLexicalPreservationEnabled(true);
    }

    @ParameterizedTest
    @CsvSource(
            delimiter = '|',
            value = {
                "class A { void m() { java.util.Map<String, Integer> a = null; } } | class A { void m() { Map<String, Integer> a = null; } }",
                "class A { java.util.Map<java.util.List<String>,Integer> a; } | class A { Map<java.util.List<String>,Integer> a; }",
                "class A { void m() { java.util.Map<String,Integer> a, b; } } | class A { void m() { Map<String,Integer> a, b; } }",
                "class A { java.util.Map<String,Integer> a, b; } | class A { Map<String,Integer> a, b; }",
                "class A { java.util.Map<String,Integer> a[]; } | class A { Map<String,Integer> a[]; }",
                "class A { java.util.Map<String,Integer> m() { return null; } } | class A { Map<String,Integer> m() { return null; } }"
            })
    void removeScope(String code, String expected) {
        considerCode(code);

        clearMapScopes();

        assertEquals(expected, LexicalPreservingPrinter.print(cu));
    }

    @Test
    void removeScopeFromOuterTypeKeepsNestedTypeAndFormatting() {
        String code = "package testpackage;\n"
                + "\n"
                + "public class TestClass\n"
                + "{\n"
                + "    public void method1()\n"
                + "    {\n"
                + "        // Map and Map.Entry\n"
                + "\n"
                + "        java.util.Map<Object, String> m = null;\n"
                + "        java.util.Map.Entry<Long, Integer> m1 = null;\n"
                + "    }\n"
                + "}\n";
        considerCode(code);

        clearMapScopes();

        assertEquals(code.replace("java.util.Map", "Map"), LexicalPreservingPrinter.print(cu));
    }

    @ParameterizedTest
    @CsvSource(
            delimiter = '|',
            value = {
                "class A { java.util.Map<String,Integer> a  =  null; } | class A { collections.Map<String,Integer> a  =  null; }",
                "class A { void m() { java.util.Map<String,Integer> a, b; } } | class A { void m() { collections.Map<String,Integer> a, b; } }",
                "class A { java.util.Map<String,Integer> a, b; } | class A { collections.Map<String,Integer> a, b; }",
                "class A { java.util.Map<String,Integer> m() { return null; } } | class A { collections.Map<String,Integer> m() { return null; } }"
            })
    void replaceScopeKeepsTypeArgumentsAndDeclarationFormatting(String code, String expected) {
        considerCode(code);

        cu.findAll(ClassOrInterfaceType.class, type -> type.getNameAsString().equals("Map"))
                .forEach(type -> type.setScope(new ClassOrInterfaceType(null, "collections")));

        assertEquals(expected, LexicalPreservingPrinter.print(cu));
    }

    @Test
    void canEditSharedScopeMoreThanOnce() {
        String unqualified = "class A { Map<String,Integer> a, b; }";
        considerCode(unqualified.replace("Map", "java.util.Map"));

        clearMapScopes();
        assertEquals(unqualified, LexicalPreservingPrinter.print(cu));

        cu.findAll(ClassOrInterfaceType.class, type -> type.getNameAsString().equals("Map"))
                .forEach(type -> type.setScope(new ClassOrInterfaceType(null, "collections")));
        assertEquals(unqualified.replace("Map", "collections.Map"), LexicalPreservingPrinter.print(cu));

        cu.findAll(ClassOrInterfaceType.class, type -> type.getNameAsString().equals("Map"))
                .forEach(type -> type.setScope(new ClassOrInterfaceType(null, "library")));
        assertEquals(unqualified.replace("Map", "library.Map"), LexicalPreservingPrinter.print(cu));

        cu.findAll(ClassOrInterfaceType.class, type -> type.getNameAsString().equals("Map"))
                .forEach(type -> type.setScope(null));
        assertEquals(unqualified, LexicalPreservingPrinter.print(cu));
    }

    @Test
    void removeScopePreservesCommentsAndSpacing() {
        considerCode("class A { java.util./* keep */Map< String /* key */, Integer > a  =  null; }");

        clearMapScopes();

        assertEquals(
                "class A { /* keep */Map< String /* key */, Integer > a  =  null; }",
                LexicalPreservingPrinter.print(cu));
    }

    @Test
    void canRequalifyAnnotatedType() {
        considerCode("class A { java.util.@Deprecated Map<String,Integer> a; }");
        ClassOrInterfaceType type = cu.findFirst(
                        ClassOrInterfaceType.class, t -> t.getNameAsString().equals("Map"))
                .get();

        type.setScope(null);
        type.setScope(new ClassOrInterfaceType(null, "collections"));

        assertEquals("class A { collections.@Deprecated Map<String,Integer> a; }", LexicalPreservingPrinter.print(cu));
    }

    @Test
    void scopeChangeKeepsLaterDeclarationAndTypeArgumentChanges() {
        considerCode("class A { java.util.Map<java.util.List<String>, Integer> a; }");
        ClassOrInterfaceType list = cu.findFirst(ClassOrInterfaceType.class, type -> type.getNameAsString()
                        .equals("List"))
                .get();

        clearMapScopes();
        list.setScope(new ClassOrInterfaceType(null, "collections"));
        list.getTypeArguments().get().set(0, new ClassOrInterfaceType(null, "Long"));
        cu.findFirst(FieldDeclaration.class).get().addModifier(Modifier.Keyword.PUBLIC);

        assertEquals("class A { public Map<collections.List<Long>, Integer> a; }", LexicalPreservingPrinter.print(cu));
    }

    @ParameterizedTest
    @CsvSource({
        "'java.util.Map<String,Integer> a, b;'",
        "'java.util.Map<String,Integer> a[], b[];'",
        "'java.util.Map<String,Integer>[] a[], b;'",
        "'java.util.Map<String,Integer>[] a, b[];'"
    })
    void scopeChangeKeepsSharedTypeForLaterFieldChanges(String declaration) {
        considerCode("class A { " + declaration + " }");
        FieldDeclaration field = cu.findFirst(FieldDeclaration.class).get();

        clearMapScopes();

        assertTrue(field.getMaximumCommonType().isPresent());
        field.addModifier(Modifier.Keyword.PUBLIC);
        assertEquals(
                "class A { public " + declaration.replace("java.util.Map", "Map") + " }",
                LexicalPreservingPrinter.print(cu));
    }

    @Test
    void scopeChangeKeepsSharedTypeForLaterLocalChanges() {
        considerCode("class A { void m() { java.util.Map<String,Integer> a = null, b = null; } }");
        VariableDeclarationExpr declaration =
                cu.findFirst(VariableDeclarationExpr.class).get();

        clearMapScopes();

        assertTrue(declaration.getMaximumCommonType().isPresent());
        declaration.addModifier(Modifier.Keyword.FINAL);
        assertEquals(
                "class A { void m() { final Map<String,Integer> a = null, b = null; } }",
                LexicalPreservingPrinter.print(cu));
    }

    private void clearMapScopes() {
        cu.findAll(
                        ClassOrInterfaceType.class,
                        type -> type.getNameAsString().equals("Map")
                                && type.getScope()
                                        .map(Object::toString)
                                        .filter("java.util"::equals)
                                        .isPresent())
                .forEach(type -> type.setScope(null));
    }
}
