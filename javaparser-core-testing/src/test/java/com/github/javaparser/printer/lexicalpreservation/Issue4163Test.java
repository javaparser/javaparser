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

package com.github.javaparser.printer.lexicalpreservation;

import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.javaparser.printer.DefaultPrettyPrinter;
import com.github.javaparser.printer.Printer;
import com.github.javaparser.printer.configuration.DefaultConfigurationOption;
import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration;
import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration.ConfigOption;
import com.github.javaparser.printer.configuration.PrinterConfiguration;
import org.junit.jupiter.api.Test;

public class Issue4163Test extends AbstractLexicalPreservingTest {

    @Test
    void test() {
        VoidVisitorAdapter<Object> visitor = new VoidVisitorAdapter<Object>() {
            @Override
            public void visit(MethodDeclaration n, Object arg) {
                System.out.println(n.getDeclarationAsString(true, true, true));
                System.out.println(n.getComment());
            }
        };
        String code = "class Foo {\n" + "		/*\n" + "      * comment\n" + "      */\n" + "		void m() {}\n" + "	}";

        // setup pretty printer to print comments
        PrinterConfiguration config = new DefaultPrinterConfiguration()
                .addOption(new DefaultConfigurationOption(ConfigOption.PRINT_COMMENTS));
        Printer printer = new DefaultPrettyPrinter(config);
        CompilationUnit cu = StaticJavaParser.parse(code);
        MethodDeclaration md = cu.findFirst(MethodDeclaration.class).get();

        // expected result is
        String expected = md.getComment().get().asString() + "\n";

        // set the new pretty printer in the compilation unit
        cu.printer(printer);
        // visit the MethodDeclaration node
        visitor.visit(cu, null);
        // checks that the comment is printed after executing the getDeclarationAsString method
        assertEqualsStringIgnoringEol(expected, md.getComment().get().toString());
    }
}
