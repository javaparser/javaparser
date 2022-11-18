
/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2019 The JavaParser Team.
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

import static org.hamcrest.CoreMatchers.equalTo;
import static org.hamcrest.MatcherAssert.assertThat;

import org.junit.jupiter.api.Test;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.ImportDeclaration;

class Issue2806Test {

    private JavaParser javaParser;

    @Test
    void importIsAddedOnTheSameLine() {
        String junit4 = "import java.lang.IllegalArgumentException;\n" +
                "\n" +
                "public class A {\n" +
                "}";
        String junit5 = "import java.lang.IllegalArgumentException;\n" +
                "import java.nio.file.Paths;\n" +
                "\n" +
                "public class A {\n" +
                "}";
        JavaParser parser = new JavaParser(new ParserConfiguration().setLexicalPreservationEnabled(true));
        CompilationUnit cu = parser.parse(junit4).getResult().get();
        LexicalPreservingPrinter.setup(cu);
        ImportDeclaration importDeclaration = new ImportDeclaration("java.nio.file.Paths", false, false);
        CompilationUnit compilationUnit = cu.addImport(importDeclaration);
        String out = LexicalPreservingPrinter.print(compilationUnit);
        assertThat(out, equalTo(junit5));
    }

}
