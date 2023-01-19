/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2023 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.resolution.javaparser.contexts;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.AssignExpr;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 *
 */
class BlockStmtContextResolutionTest extends AbstractResolutionTest {

    @BeforeEach
    void setup() {
    }

    // issue #3526
    @Test
    void must_be_resolved_from_previous_declaration(){
        String src = "public class Example {\n"
                + "    int a = 3;\n"
                + "    public void bla() {\n"
                + "        a = 7; // 'a' must be resolved as int not String\n"
                + "        String a = \"\";\n"
                + "        a = \"test\";\n"
                + "    }\n"
                + "}";
        ParserConfiguration configuration = new ParserConfiguration()
                .setSymbolResolver(new JavaSymbolSolver(new CombinedTypeSolver(new ReflectionTypeSolver())));
        StaticJavaParser.setConfiguration(configuration);
        CompilationUnit cu = StaticJavaParser.parse(src);
        AssignExpr expr = cu.findFirst(AssignExpr.class).get();
        ResolvedType rt = expr.calculateResolvedType();
        assertEquals("int", rt.describe());
    }
    
    @Test
    void must_be_resolved_from_previous_declaration_second_declaration_of_the_same_field_name(){
        String src = "public class Example {\n"
                + "    int a = 3;\n"
                + "    public void bla() {\n"
                + "        a = 7; // 'a' must be resolved as int not String\n"
                + "        String a = \"\";\n"
                + "        a = \"test\";\n"
                + "    }\n"
                + "}";
        ParserConfiguration configuration = new ParserConfiguration()
                .setSymbolResolver(new JavaSymbolSolver(new CombinedTypeSolver(new ReflectionTypeSolver())));
        StaticJavaParser.setConfiguration(configuration);
        CompilationUnit cu = StaticJavaParser.parse(src);
        AssignExpr expr = cu.findAll(AssignExpr.class).get(1);
        ResolvedType rt2 = expr.calculateResolvedType();
        assertEquals("java.lang.String", rt2.describe());
    }

}
