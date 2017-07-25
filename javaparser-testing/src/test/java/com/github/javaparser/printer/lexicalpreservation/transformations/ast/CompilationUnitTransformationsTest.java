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

package com.github.javaparser.printer.lexicalpreservation.transformations.ast;

import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.printer.lexicalpreservation.AbstractLexicalPreservingTest;
import org.junit.Test;

import java.io.IOException;

import static com.github.javaparser.utils.Utils.EOL;

/**
 * Transforming CompilationUnit and verifying the LexicalPreservation works as expected.
 */
public class CompilationUnitTransformationsTest extends AbstractLexicalPreservingTest {

    // packageDeclaration

    @Test
    public void addingPackageDeclaration() throws IOException {
        considerCode("class A {}");
        cu.setPackageDeclaration(new PackageDeclaration(new Name(new Name("foo"), "bar")));
        assertTransformedToString("package foo.bar;"+ EOL + EOL + "class A {}", cu);
    }

    @Test
    public void removingPackageDeclaration() throws IOException {
        considerCode("package foo.bar; class A {}");
        cu.removePackageDeclaration();
        assertTransformedToString("class A {}", cu);
    }

    @Test
    public void replacingPackageDeclaration() throws IOException {
        considerCode("package foo.bar; class A {}");
        cu.setPackageDeclaration(new PackageDeclaration(new Name(new Name("foo2"), "baz")));
        assertTransformedToString("package foo2.baz;" +
                EOL + EOL +
                " class A {}", cu);
    }

    // imports

    // types
}
