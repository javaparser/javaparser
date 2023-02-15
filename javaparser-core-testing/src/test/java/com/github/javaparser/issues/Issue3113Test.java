/*
 * Copyright (C) 2013-2023 The JavaParser Team.
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

package com.github.javaparser.issues;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.stmt.SwitchStmt;
import com.github.javaparser.printer.lexicalpreservation.AbstractLexicalPreservingTest;
import com.github.javaparser.printer.lexicalpreservation.LexicalPreservingPrinter;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class Issue3113Test extends AbstractLexicalPreservingTest {
    @Test
    public void issue3113() {
        StaticJavaParser.getConfiguration().setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_12);

        String originalSourceCode = "public class HelloWorld {\n" +
                "  public static void main(String[] args) {\n" +
                "      final int value = 2;\n" +
                "      String numericString;\n" +
                "      switch (value)\n" +
                "      {\n" +
                "       case 1 -> numericString = \"one\";\n" +
                "       default -> numericString = \"N/A\";\n" +
                "      }\n" +
                "      System.out.println(\"value:\" + value + \" as string: \" + numericString);\n" +
                "  }\n" +
                "}\n";

        CompilationUnit cu = StaticJavaParser.parse(originalSourceCode);
        LexicalPreservingPrinter.setup(cu);
        SwitchStmt expr = cu.findFirst(SwitchStmt.class).get();
        String modifiedSourceCode = LexicalPreservingPrinter.print(expr);
        assertEquals("switch (value)\n" +
                "      {\n" +
                "       case 1 -> numericString = \"one\";\n" +
                "       default -> numericString = \"N/A\";\n" +
                "      }", modifiedSourceCode);
    }
}
