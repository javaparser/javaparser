
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

import static org.junit.jupiter.api.Assertions.assertEquals;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Test;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;

class Issue1793Test {
    
    @AfterEach
    public void reset() {
        StaticJavaParser.setConfiguration(new ParserConfiguration());
    }

    @Test
    void importIsAddedOnTheSameLine() {
        String src = 
                "public class Test {\n" + 
                "  public void foo(Bar x, Bar y) {\n" + 
                "    x.barf(); // expected to be wrapped\n" + 
                "    x.bark(); // expected to be wrapped\n" + 
                "    y.barf(); // expected to be wrapped\n" + 
                "    y.bark(); // expected to be wrapped\n" + 
                "  }\n" + 
                "}";
        StaticJavaParser.setConfiguration(new ParserConfiguration().setLexicalPreservationEnabled(true));
        CompilationUnit cu = StaticJavaParser.parse(src);
        LexicalPreservingPrinter.setup(cu);
        assertEquals(LexicalPreservingPrinter.print(cu), LexicalPreservingPrinter.print(cu.clone()));
    }

}
