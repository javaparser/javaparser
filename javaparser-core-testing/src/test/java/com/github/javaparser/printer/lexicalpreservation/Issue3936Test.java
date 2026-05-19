/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
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

import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;

import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.TextBlockLiteralExpr;
import org.junit.jupiter.api.Test;

public class Issue3936Test extends AbstractLexicalPreservingTest {
    static final String given = """
            package some.project;
            
            import java.util.Optional;
            
            public class SomeClass {
            
            	String html = "" + "<html>\\n"
            			+ "\\t<head>\\n"
            			+ "\\t\\t<meta charset=\\"utf-8\\">\\n"
            			+ "\\t</head>\\n"
            			+ "\\t<body class=\\"default-view\\" style=\\"word-wrap: break-word;\\">\\n"
            			+ "\\t\\t<p>Hello, world</p>\\n"
            			+ "\\t</body>\\n"
            			+ "</html>\\n";
            }\
            """;

    @Test
    void test() {
        considerCode(given);

        String newText = "\tfirstRow\n\tsecondRow\n\tthirdRow";

        LexicalPreservingPrinter.setup(cu);

        VariableDeclarator expr = cu.findFirst(VariableDeclarator.class).get();
        expr.setInitializer(new TextBlockLiteralExpr(newText));

        String actual = LexicalPreservingPrinter.print(cu);
        String expected = """
                package some.project;
                
                import java.util.Optional;
                
                public class SomeClass {
                
                	String html = ""\"
                	firstRow
                	secondRow
                	thirdRow""\";
                }\
                """;
        assertEqualsStringIgnoringEol(expected, actual);
    }
}
