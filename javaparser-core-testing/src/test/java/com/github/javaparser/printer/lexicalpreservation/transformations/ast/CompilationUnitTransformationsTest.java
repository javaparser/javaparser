/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2024 The JavaParser Team.
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

package com.github.javaparser.printer.lexicalpreservation.transformations.ast;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.printer.lexicalpreservation.AbstractLexicalPreservingTest;
import com.github.javaparser.utils.LineSeparator;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

/**
 * Transforming CompilationUnit and verifying the LexicalPreservation works as expected.
 */
class CompilationUnitTransformationsTest extends AbstractLexicalPreservingTest {

    @BeforeEach
    void initParser() {
        StaticJavaParser.getParserConfiguration().setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_25);
    }

    // packageDeclaration

    @Test
    void addingPackageDeclaration() {
        considerCode("class A {}");
        cu.setPackageDeclaration(new PackageDeclaration(new Name(new Name("foo"), "bar")));
        assertTransformedToString("package foo.bar;" + LineSeparator.SYSTEM + LineSeparator.SYSTEM + "class A {}", cu);
    }

    @Test
    void removingPackageDeclaration() {
        considerCode("package foo.bar; class A {}");
        cu.removePackageDeclaration();
        assertTransformedToString("class A {}", cu);
    }

    @Test
    void replacingPackageDeclaration() {
        considerCode("package foo.bar; class A {}");
        cu.setPackageDeclaration(new PackageDeclaration(new Name(new Name("foo2"), "baz")));
        assertTransformedToString(
                "package foo2.baz;" + LineSeparator.SYSTEM + LineSeparator.SYSTEM + " class A {}", cu);
    }

    // imports

    @Test
    void addingModuleImport() {
        considerCode("class A {}");
        cu.addImport("java.base", false, false, true);
        assertTransformedToString(
                "import module java.base;" + LineSeparator.SYSTEM + LineSeparator.SYSTEM + "class A {}", cu);
    }

    @Test
    void removingModuleImport() {
        considerCode("import module java.base; class A {}");
        cu.remove(cu.getImport(0));
        assertTransformedToString("class A {}", cu);
    }

    @Test
    void modifyingModuleImport() {
        considerCode("import module java.base; class A {}");
        cu.getImport(0).setName("a.b");
        assertTransformedToString("import module a.b; class A {}", cu);
    }

    // types
}
