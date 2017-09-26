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

import static com.github.javaparser.utils.Utils.EOL;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.List;
import java.util.Map;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.AnnotationDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;

public class CompilationUnitBuildersTest {
    private final CompilationUnit cu = new CompilationUnit();

    @Test
    public void testAddImport() {
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

    class testInnerClass {

    }

    @Test
    public void testAddImportAnonymousClass() {
        cu.addImport(testInnerClass.class);
        assertEquals("import " + testInnerClass.class.getName().replace("$", ".") + ";" + EOL,
                cu.getImport(0).toString());
    }

    @Test(expected = RuntimeException.class)
    public void testAddImportInnerClass() {
        Object anonymous = new Object() {

        };
        cu.addImport(anonymous.getClass());
    }

    @Test
    public void testAddClass() {
        ClassOrInterfaceDeclaration myClassDeclaration = cu.addClass("testClass", Modifier.PRIVATE);
        assertEquals(1, cu.getTypes().size());
        assertEquals("testClass", cu.getType(0).getNameAsString());
        assertEquals(ClassOrInterfaceDeclaration.class, cu.getType(0).getClass());
        assertTrue(myClassDeclaration.isPrivate());
        assertFalse(myClassDeclaration.isInterface());
    }

    @Test
    public void testAddInterface() {
        ClassOrInterfaceDeclaration myInterfaceDeclaration = cu.addInterface("testInterface");
        assertEquals(1, cu.getTypes().size());
        assertEquals("testInterface", cu.getType(0).getNameAsString());
        assertTrue(myInterfaceDeclaration.isPublic());
        assertEquals(ClassOrInterfaceDeclaration.class, cu.getType(0).getClass());
        assertTrue(myInterfaceDeclaration.isInterface());
    }

    @Test
    public void testAddEnum() {
        EnumDeclaration myEnumDeclaration = cu.addEnum("test");
        assertEquals(1, cu.getTypes().size());
        assertEquals("test", cu.getType(0).getNameAsString());
        assertTrue(myEnumDeclaration.isPublic());
        assertEquals(EnumDeclaration.class, cu.getType(0).getClass());
    }

    @Test
    public void testAddAnnotationDeclaration() {
        AnnotationDeclaration myAnnotationDeclaration = cu.addAnnotationDeclaration("test");
        assertEquals(1, cu.getTypes().size());
        assertEquals("test", cu.getType(0).getNameAsString());
        assertTrue(myAnnotationDeclaration.isPublic());
        assertEquals(AnnotationDeclaration.class, cu.getType(0).getClass());
    }

    @Test
    public void testGetClassByName() {
        assertEquals(cu.addClass("test"), cu.getClassByName("test").get());
    }

    @Test
    public void testGetInterfaceByName() {
        assertEquals(cu.addInterface("test"), cu.getInterfaceByName("test").get());
    }

    @Test
    public void testGetEnumByName() {
        assertEquals(cu.addEnum("test"), cu.getEnumByName("test").get());
    }

    @Test
    public void testGetAnnotationDeclarationByName() {
        assertEquals(cu.addAnnotationDeclaration("test"), cu.getAnnotationDeclarationByName("test").get());
    }
}
