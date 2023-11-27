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

package com.github.javaparser.ast;

import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parse;
import static com.github.javaparser.StaticJavaParser.parsePackageDeclaration;
import static com.github.javaparser.utils.Utils.SYSTEM_EOL;
import static org.junit.jupiter.api.Assertions.assertEquals;

class ReplaceNodeTest {
    @Test
    void testSimplePropertyWithGenericReplace() {
        CompilationUnit cu = parse("package x; class Y {}");
        cu.replace(cu.getPackageDeclaration().get(), parsePackageDeclaration("package z;"));
        assertEquals(String.format("package z;%1$s" +
                "%1$s" +
                "class Y {%1$s" +
                "}%1$s", SYSTEM_EOL), cu.toString());
    }

    @Test
    void testListProperty() {
        CompilationUnit cu = parse("package x; class Y {}");
        cu.replace(cu.getClassByName("Y").get(), parse("class B{int y;}").getClassByName("B").get());
        assertEquals(String.format("package x;%1$s" +
                "%1$s" +
                "class B {%1$s" +
                "%1$s" +
                "    int y;%1$s" +
                "}%1$s", SYSTEM_EOL), cu.toString());
    }
}
