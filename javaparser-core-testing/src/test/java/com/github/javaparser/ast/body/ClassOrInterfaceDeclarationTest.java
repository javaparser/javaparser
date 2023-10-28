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

package com.github.javaparser.ast.body;

import static com.github.javaparser.StaticJavaParser.parse;
import static com.github.javaparser.StaticJavaParser.parseBodyDeclaration;
import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;
import org.opentest4j.AssertionFailedError;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.utils.TestParser;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.TypeParameter;

class ClassOrInterfaceDeclarationTest {
    @Test
    void staticNestedClass() {
        CompilationUnit cu = parse("class X{static class Y{}}");
        ClassOrInterfaceDeclaration y = cu.getClassByName("X").get().getMembers().get(0).asClassOrInterfaceDeclaration();

        assertFalse(y.isInnerClass());
        assertTrue(y.isNestedType());
        assertFalse(y.isLocalClassDeclaration());
    }

    @Test
    void nestedInterface() {
        CompilationUnit cu = parse("class X{interface Y{}}");
        ClassOrInterfaceDeclaration y = cu.getClassByName("X").get().getMembers().get(0).asClassOrInterfaceDeclaration();

        assertFalse(y.isInnerClass());
        assertTrue(y.isNestedType());
        assertFalse(y.isLocalClassDeclaration());
    }

    @Test
    void nonStaticNestedClass() {
        CompilationUnit cu = parse("class X{class Y{}}");
        ClassOrInterfaceDeclaration y = cu.getClassByName("X").get().getMembers().get(0).asClassOrInterfaceDeclaration();

        assertTrue(y.isInnerClass());
        assertTrue(y.isNestedType());
        assertFalse(y.isLocalClassDeclaration());
    }

    @Test
    void topClass() {
        CompilationUnit cu = parse("class X{}");
        ClassOrInterfaceDeclaration y = cu.getClassByName("X").get();

        assertFalse(y.isInnerClass());
        assertFalse(y.isNestedType());
        assertFalse(y.isLocalClassDeclaration());
    }

    @Test
    void localClass() {
        MethodDeclaration method = parseBodyDeclaration("void x(){class X{};}").asMethodDeclaration();
        ClassOrInterfaceDeclaration x = method.findFirst(ClassOrInterfaceDeclaration.class).get();

        assertFalse(x.isInnerClass());
        assertFalse(x.isNestedType());
        assertTrue(x.isLocalClassDeclaration());
    }

    @Test
    void sealedClass() {
        CompilationUnit cu = TestParser.parseCompilationUnit(ParserConfiguration.LanguageLevel.JAVA_17, "sealed class X permits Y, Z {}");
        ClassOrInterfaceDeclaration x = cu.getClassByName("X").get();

        assertFalse(x.isInnerClass());
        assertFalse(x.isNestedType());
        assertFalse(x.isLocalClassDeclaration());
        assertTrue(x.hasModifier(Modifier.Keyword.SEALED));
        assertEquals(x.getPermittedTypes().size(), 2);
        assertEquals(x.getPermittedTypes().get(0).getNameAsString(), "Y");
        assertEquals(x.getPermittedTypes().get(1).getNameAsString(), "Z");
    }

    @Test
    void nonSealedClass() {
        CompilationUnit cu = TestParser.parseCompilationUnit(ParserConfiguration.LanguageLevel.JAVA_17, "non-sealed class X{}");
        ClassOrInterfaceDeclaration x = cu.getClassByName("X").get();

        assertFalse(x.isInnerClass());
        assertFalse(x.isNestedType());
        assertFalse(x.isLocalClassDeclaration());
        assertTrue(x.hasModifier(Modifier.Keyword.NON_SEALED));
    }

    @ParameterizedTest
    @EnumSource(value = ParserConfiguration.LanguageLevel.class, names = {"JAVA_8","JAVA_9","JAVA_10","JAVA_11","JAVA_12","JAVA_13","JAVA_14", "JAVA_15", "JAVA_16"})
    void sealedFieldNamePermitted(ParserConfiguration.LanguageLevel languageLevel) {
    	assertDoesNotThrow(() -> {
    		TestParser.parseVariableDeclarationExpr(languageLevel, "boolean sealed");
        });
    }

    @ParameterizedTest
    @EnumSource(value = ParserConfiguration.LanguageLevel.class, names = {"JAVA_17"})
    void sealedFieldNameNotPermitted(ParserConfiguration.LanguageLevel languageLevel) {
    	assertThrows(AssertionFailedError.class, () -> {
    		TestParser.parseVariableDeclarationExpr(languageLevel, "boolean sealed");
        });
    }

    @ParameterizedTest
    @EnumSource(value = ParserConfiguration.LanguageLevel.class, names = {"JAVA_8","JAVA_9","JAVA_10","JAVA_11","JAVA_12","JAVA_13","JAVA_14", "JAVA_15", "JAVA_16"})
    void permitsFieldNamePermitted(ParserConfiguration.LanguageLevel languageLevel) {
    	assertDoesNotThrow(() -> {
    		TestParser.parseVariableDeclarationExpr(languageLevel, "boolean permits");
        });
    }

    @ParameterizedTest
    @EnumSource(value = ParserConfiguration.LanguageLevel.class, names = {"JAVA_17"})
    void permitsFieldNameNotPermitted(ParserConfiguration.LanguageLevel languageLevel) {
    	assertThrows(AssertionFailedError.class, () -> {
    		TestParser.parseVariableDeclarationExpr(languageLevel, "boolean permits");
        });
    }

    @Test
    public void testClassOrInterfaceDeclarationDefaultConstructor() {
        ClassOrInterfaceDeclaration decl = new ClassOrInterfaceDeclaration();
        assertNotNull(decl);
    }

    @Test
    public void testClassOrInterfaceDeclarationWithModifiersAndName() {
        ClassOrInterfaceDeclaration decl = new ClassOrInterfaceDeclaration(new NodeList<>(), false, "TestName");
        assertEquals("TestName", decl.getNameAsString());
    }

    @Test
    public void testCloneMethod() {
        ClassOrInterfaceDeclaration decl = new ClassOrInterfaceDeclaration();
        ClassOrInterfaceDeclaration cloned = decl.clone();
        assertNotNull(cloned);
    }

    @Test
    public void testRemoveMethodExtendedTypes() {
        ClassOrInterfaceDeclaration decl = new ClassOrInterfaceDeclaration();
        ClassOrInterfaceType extendedType = new ClassOrInterfaceType("ExtendedType");
        decl.addExtendedType(extendedType);
        assertTrue(decl.remove(extendedType));
        assertFalse(decl.getExtendedTypes().contains(extendedType));
    }

    @Test
    public void testRemoveMethodImplementedTypes() {
        ClassOrInterfaceDeclaration decl = new ClassOrInterfaceDeclaration();
        ClassOrInterfaceType implementedType = new ClassOrInterfaceType("ImplementedType");
        decl.addImplementedType(implementedType);
        assertTrue(decl.remove(implementedType));
        assertFalse(decl.getImplementedTypes().contains(implementedType));
    }

    @Test
    public void testRemoveMethodTypeParameters() {
        ClassOrInterfaceDeclaration decl = new ClassOrInterfaceDeclaration();
        TypeParameter typeParameter = new TypeParameter("TypeParam");
        decl.addTypeParameter(typeParameter);
        assertTrue(decl.remove(typeParameter));
        assertFalse(decl.getTypeParameters().contains(typeParameter));
    }

    @Test
    public void testGetFullyQualifiedNameNonLocalClass() {
        CompilationUnit cu = parse("package com.example; class X{}");
        ClassOrInterfaceDeclaration y = cu.getClassByName("X").get();
        assertEquals("com.example.X", y.getFullyQualifiedName().get());
    }

    @Test
    public void testReplaceExtendedTypes() {
        ClassOrInterfaceDeclaration decl = new ClassOrInterfaceDeclaration();
        ClassOrInterfaceType oldType = new ClassOrInterfaceType("OldType");
        ClassOrInterfaceType newType = new ClassOrInterfaceType("NewType");
        decl.addExtendedType(oldType);
        boolean result = decl.replace(oldType, newType);
        assertTrue(result);
        assertTrue(decl.getExtendedTypes().contains(newType));
    }

    @Test
    public void testReplaceImplementedTypes() {
        ClassOrInterfaceDeclaration decl = new ClassOrInterfaceDeclaration();
        ClassOrInterfaceType oldType = new ClassOrInterfaceType("OldType");
        ClassOrInterfaceType newType = new ClassOrInterfaceType("NewType");
        decl.addImplementedType(oldType);
        boolean result = decl.replace(oldType, newType);
        assertTrue(result);
        assertTrue(decl.getImplementedTypes().contains(newType));
    }

    @Test
    public void testReplaceTypeParameters() {
        ClassOrInterfaceDeclaration decl = new ClassOrInterfaceDeclaration();
        TypeParameter oldType = new TypeParameter("OldType");
        TypeParameter newType = new TypeParameter("NewType");
        decl.addTypeParameter(oldType);
        boolean result = decl.replace(oldType, newType);
        assertTrue(result);
        assertTrue(decl.getTypeParameters().contains(newType));
    }

    @Test
    void testTypeCastingMethods() {
        ClassOrInterfaceDeclaration decl = new ClassOrInterfaceDeclaration();
        assertTrue(decl.isClassOrInterfaceDeclaration());
        assertEquals(decl, decl.asClassOrInterfaceDeclaration());

        decl.ifClassOrInterfaceDeclaration(e -> {
            assertTrue(e instanceof ClassOrInterfaceDeclaration);
        });

        assertTrue(decl.toClassOrInterfaceDeclaration().isPresent());
    }
}
