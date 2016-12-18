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

package com.github.javaparser.ast.imports;

import com.github.javaparser.JavaParser;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class ImportDeclarationTest {
    @Test
    public void singleTypeImportDeclaration() {
        ImportDeclaration importDeclaration = JavaParser.parseImport("import a.b.c.X;");
        SingleTypeImportDeclaration i = (SingleTypeImportDeclaration) importDeclaration;
        assertEquals("a.b.c.X", i.getType().toString());
    }

    @Test
    public void typeImportOnDemandDeclaration() {
        ImportDeclaration importDeclaration = JavaParser.parseImport("import a.b.c.D.*;");
        TypeImportOnDemandDeclaration i = (TypeImportOnDemandDeclaration) importDeclaration;
        assertEquals("a.b.c.D", i.getName().toString());
        assertEquals("D", i.getName().getIdentifier());
    }

    @Test
    public void singleStaticImportDeclaration() {
        ImportDeclaration importDeclaration = JavaParser.parseImport("import static a.b.c.X.def;");
        SingleStaticImportDeclaration i = (SingleStaticImportDeclaration) importDeclaration;
        assertEquals("a.b.c.X", i.getType().toString());
        assertEquals("def", i.getStaticMember());
    }

    @Test
    public void staticImportOnDemandDeclaration() {
        ImportDeclaration importDeclaration = JavaParser.parseImport("import static a.b.c.X.*;");
        StaticImportOnDemandDeclaration i = (StaticImportOnDemandDeclaration) importDeclaration;
        assertEquals("X", i.getType().getNameAsString());
        assertEquals("c", i.getType().getScope().get().getNameAsString());
        assertEquals("b", i.getType().getScope().get().getScope().get().getNameAsString());
        assertEquals("a", i.getType().getScope().get().getScope().get().getScope().get().getNameAsString());
    }

}