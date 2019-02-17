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

package com.github.javaparser.builders;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.AnnotationDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import org.junit.jupiter.api.Test;

import java.lang.annotation.ElementType;
import java.util.List;
import java.util.Map;

import static com.github.javaparser.StaticJavaParser.parseImport;
import static com.github.javaparser.ast.Modifier.Keyword.PRIVATE;
import static com.github.javaparser.utils.Utils.EOL;
import static org.junit.jupiter.api.Assertions.*;
import static org.junit.jupiter.api.Assertions.assertThrows;

class CompilationUnitBuildersTest {
    private final CompilationUnit cu = new CompilationUnit();

    @Test
    void testAddImport() {
        cu.addImport(Map.class);
        cu.addImport(Map.class);
        cu.addImport(List.class);
        assertEquals(2, cu.getImports().size());
        cu.addImport("myImport");
        assertEquals(3, cu.getImports().size());
        assertEquals("import " + Map.class.getName() + ";" + EOL, cu.getImport(0).toString());
        assertEquals("import " + List.class.getName() + ";" + EOL, cu.getImport(1).toString());
        assertEquals("import myImport;" + EOL, cu.getImport(2).toString());
    }

    @Test
    void typesInTheJavaLangPackageDoNotNeedExplicitImports() {
        cu.addImport(String.class);
        assertEquals(0, cu.getImports().size());
    }

    @Test
    void typesInSubPackagesOfTheJavaLangPackageRequireExplicitImports() {
        cu.addImport(ElementType.class);
        assertEquals(1, cu.getImports().size());
        assertEquals("import java.lang.annotation.ElementType;"+ EOL, cu.getImport(0).toString());
    }

    @Test
    void doNotAddDuplicateImportsByClass() {
        cu.addImport(Map.class);
        cu.addImport(Map.class);
        assertEquals(1, cu.getImports().size());
    }

    @Test
    void doNotAddDuplicateImportsByString() {
        cu.addImport(Map.class);
        cu.addImport("java.util.Map");
        assertEquals(1, cu.getImports().size());
    }

    @Test
    void doNotAddDuplicateImportsByStringAndFlags() {
        cu.addImport(Map.class);
        cu.addImport("java.util.Map", false, false);
        assertEquals(1, cu.getImports().size());
    }

    @Test
    void doNotAddDuplicateImportsByImportDeclaration() {
        cu.addImport(Map.class);
        cu.addImport(parseImport("import java.util.Map;"));
        assertEquals(1, cu.getImports().size());
    }

    @Test
    void testAddImportArrayTypes() {
        cu.addImport(CompilationUnit[][][].class);
        cu.addImport(int[][][].class);
        cu.addImport(Integer[][][].class);
        cu.addImport(List[][][].class);
        assertEquals(2, cu.getImports().size());
        assertEquals("com.github.javaparser.ast.CompilationUnit", cu.getImport(0).getNameAsString());
        assertEquals("java.util.List", cu.getImport(1).getNameAsString());
    }

    class testInnerClass {

    }

    @Test
    void testAddImportAnonymousClass() {
        cu.addImport(testInnerClass.class);
        assertEquals("import " + testInnerClass.class.getName().replace("$", ".") + ";" + EOL,
                cu.getImport(0).toString());
    }

    @Test
    void testAddImportInnerClass() {
        assertThrows(RuntimeException.class, () -> {
            Object anonymous = new Object(){

            };
            cu.addImport(anonymous.getClass());
    });
}

    @Test
    void testAddClass() {
        ClassOrInterfaceDeclaration myClassDeclaration = cu.addClass("testClass", PRIVATE);
        assertEquals(1, cu.getTypes().size());
        assertEquals("testClass", cu.getType(0).getNameAsString());
        assertEquals(ClassOrInterfaceDeclaration.class, cu.getType(0).getClass());
        assertTrue(myClassDeclaration.isPrivate());
        assertFalse(myClassDeclaration.isInterface());
    }

    @Test
    void testAddInterface() {
        ClassOrInterfaceDeclaration myInterfaceDeclaration = cu.addInterface("testInterface");
        assertEquals(1, cu.getTypes().size());
        assertEquals("testInterface", cu.getType(0).getNameAsString());
        assertTrue(myInterfaceDeclaration.isPublic());
        assertEquals(ClassOrInterfaceDeclaration.class, cu.getType(0).getClass());
        assertTrue(myInterfaceDeclaration.isInterface());
    }

    @Test
    void testAddEnum() {
        EnumDeclaration myEnumDeclaration = cu.addEnum("test");
        assertEquals(1, cu.getTypes().size());
        assertEquals("test", cu.getType(0).getNameAsString());
        assertTrue(myEnumDeclaration.isPublic());
        assertEquals(EnumDeclaration.class, cu.getType(0).getClass());
    }

    @Test
    void testAddAnnotationDeclaration() {
        AnnotationDeclaration myAnnotationDeclaration = cu.addAnnotationDeclaration("test");
        assertEquals(1, cu.getTypes().size());
        assertEquals("test", cu.getType(0).getNameAsString());
        assertTrue(myAnnotationDeclaration.isPublic());
        assertEquals(AnnotationDeclaration.class, cu.getType(0).getClass());
    }

    @Test
    void testGetClassByName() {
        assertEquals(cu.addClass("test"), cu.getClassByName("test").get());
    }

    @Test
    void testGetInterfaceByName() {
        assertEquals(cu.addInterface("test"), cu.getInterfaceByName("test").get());
    }

    @Test
    void testGetEnumByName() {
        assertEquals(cu.addEnum("test"), cu.getEnumByName("test").get());
    }

    @Test
    void testGetAnnotationDeclarationByName() {
        assertEquals(cu.addAnnotationDeclaration("test"), cu.getAnnotationDeclarationByName("test").get());
    }
}
