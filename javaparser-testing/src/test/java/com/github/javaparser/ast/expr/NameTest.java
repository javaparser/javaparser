/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2017 The JavaParser Team.
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

package com.github.javaparser.ast.expr;

import com.github.javaparser.ParseProblemException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.printer.ConcreteSyntaxModel;
import org.junit.Test;

import static com.github.javaparser.JavaParser.*;
import static com.github.javaparser.utils.Utils.EOL;
import static org.assertj.core.api.AssertionsForInterfaceTypes.assertThat;
import static org.junit.Assert.assertEquals;

public class NameTest {
    @Test
    public void outerNameExprIsTheRightMostIdentifier() {
        Name name = parseName("a.b.c");
        assertEquals("c", name.getIdentifier());
    }

    @Test
    public void parsingAndUnparsingWorks() {
        Name name = parseName("a.b.c");
        assertEquals("a.b.c", name.asString());
    }

    @Test(expected = ParseProblemException.class)
    public void parsingEmptyNameThrowsException() {
        parseName("");
    }

    @Test
    public void nameCanHaveAnnotationsInside() {
        Name name = parseName("a.@A b. @C c");
        assertEquals("a.b.c", name.asString());
        assertThat(name.getAnnotations()).containsExactly(new MarkerAnnotationExpr("C"));
        assertThat(name.getQualifier().get().getAnnotations()).containsExactly(new MarkerAnnotationExpr("A"));

        assertEquals("a.@A b.@C c", name.toString());
        assertEquals("a.@A b.@C c", ConcreteSyntaxModel.genericPrettyPrint(name));
    }

    @Test
    public void importName() {
        ImportDeclaration importDeclaration = parseImport("import java.@Abc util.List;");

        assertThat(importDeclaration.getName().getQualifier().get().getAnnotations()).containsExactly(new MarkerAnnotationExpr("Abc"));

        assertEquals("import java.@Abc util.List;" + EOL, importDeclaration.toString());
        assertEquals("import java.@Abc util.List;" + EOL, ConcreteSyntaxModel.genericPrettyPrint(importDeclaration));
    }

    @Test
    public void packageName() {
        CompilationUnit cu = parse("package @Abc p1.p2;");

        assertThat(cu.getPackageDeclaration().get().getName().getQualifier().get().getAnnotations()).containsExactly(new MarkerAnnotationExpr("Abc"));

        assertEquals("package @Abc p1.p2;" + EOL + EOL, cu.toString());
        assertEquals("package @Abc p1.p2;" + EOL + EOL, ConcreteSyntaxModel.genericPrettyPrint(cu));
    }
}