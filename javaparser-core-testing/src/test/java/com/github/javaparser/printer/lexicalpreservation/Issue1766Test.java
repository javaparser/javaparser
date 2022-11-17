/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2019 The JavaParser Team.
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

import org.junit.jupiter.api.Test;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.utils.TestUtils;

public class Issue1766Test extends AbstractLexicalPreservingTest  {
    
    @Test
    public void testWithLexicalPreservationEnabled() {
        
        String actual = 
                "public class SimpleTestClass {\n" + 
                "  public SimpleTestClass() {\n" + 
                "    // nothing\n" + 
                "  }\n" + 
                "  @Override\n" + 
                "  void bubber() {\n" + 
                "    // nothing\n" + 
                "  }\n" +
                "}";
        
        String expected = 
                "public class SimpleTestClass {\n" + 
                "  public SimpleTestClass() {\n" + 
                "    // nothing\n" + 
                "  }\n" + 
                "  @Override\n" + 
                "  void bubber() {\n" + 
                "    // nothing\n" + 
                "  }\n" + 
                "}";
        
        final ParserConfiguration parserConfiguration = new ParserConfiguration();
        parserConfiguration.setLexicalPreservationEnabled(true);
        StaticJavaParser.setConfiguration(parserConfiguration);
      
        CompilationUnit cu = StaticJavaParser.parse(actual);
        TestUtils.assertEqualsStringIgnoringEol(expected, actual);
    }
    
    @Test
    public void testWithLexicalPreservingPrinterSetup() {
        
        String actual = 
                "public class SimpleTestClass {\n" + 
                "  public SimpleTestClass() {\n" + 
                "    // nothing\n" + 
                "  }\n" + 
                "  @Override\n" + 
                "  void bubber() {\n" + 
                "    // nothing\n" + 
                "  }\n" +
                "}";
        
        String expected = 
                "public class SimpleTestClass {\n" + 
                "  public SimpleTestClass() {\n" + 
                "    // nothing\n" + 
                "  }\n" + 
                "  @Override\n" + 
                "  void bubber() {\n" + 
                "    // nothing\n" + 
                "  }\n" + 
                "}";
        
        final ParserConfiguration parserConfiguration = new ParserConfiguration();
        StaticJavaParser.setConfiguration(parserConfiguration);
      
        CompilationUnit cu = StaticJavaParser.parse(actual);
        LexicalPreservingPrinter.setup(cu);
        TestUtils.assertEqualsStringIgnoringEol(expected, actual);
    }
}
