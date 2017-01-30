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
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import java.util.List;
import java.util.function.Function;

import static com.github.javaparser.utils.Utils.EOL;
import static org.junit.Assert.assertEquals;

public class ClassOrInterfaceDeclarationBuildersTest {
    CompilationUnit cu;

    @Before
    public void setup() {
        cu = new CompilationUnit();
    }

    @After
    public void teardown() {
        cu = null;
    }

    @Test
    public void testAddExtends() {
        ClassOrInterfaceDeclaration testClass = cu.addClass("test");
        testClass.addExtendedType(List.class);
        assertEquals(1, cu.getImports().size());
        assertEquals("import " + List.class.getName() + ";" + EOL,
                cu.getImport(0).toString());
        assertEquals(1, testClass.getExtendedTypes().size());
        assertEquals(List.class.getSimpleName(), testClass.getExtendedTypes(0).getNameAsString());
    }

    @Test
    public void testAddImplements() {
        ClassOrInterfaceDeclaration testClass = cu.addClass("test");
        testClass.addImplementedType(Function.class);
        assertEquals(1, cu.getImports().size());
        assertEquals("import " + Function.class.getName() + ";" + EOL,
                cu.getImport(0).toString());
        assertEquals(1, testClass.getImplementedTypes().size());
        assertEquals(Function.class.getSimpleName(), testClass.getImplementedTypes(0).getNameAsString());
    }
}
