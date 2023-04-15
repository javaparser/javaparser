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

package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.Statement;
import org.junit.jupiter.api.Test;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertTrue;
import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;

public class Issue2374Test extends AbstractLexicalPreservingTest {
    
    @Test
    public void test() {
        String lineComment = "Example comment";
        considerCode(
                "public class Bar {\n" + 
                "    public void foo() {\n" + 
                "        System.out.print(\"Hello\");\n" + 
                "    }\n" + 
                "}"
                );
        String expected =
        		"public class Bar {\n"
        		+ "    public void foo() {\n"
        		+ "        System.out.print(\"Hello\");\n"
        		+ "        //Example comment\n"
        		+ "        System.out.println(\"World!\");\n"
        		+ "    }\n"
        		+ "}";
        // contruct a statement with a comment
        Statement stmt = StaticJavaParser.parseStatement("System.out.println(\"World!\");");
        stmt.setLineComment(lineComment);
        // add the statement to the ast
        Optional<MethodDeclaration> md = cu.findFirst(MethodDeclaration.class);
        md.get().getBody().get().addStatement(stmt);
        // print the result from LexicalPreservingPrinter
        String result = LexicalPreservingPrinter.print(cu);
        // verify that the LexicalPreservingPrinter don't forget the comment
        assertEqualsStringIgnoringEol(expected, result);
    }
}
