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

package com.github.javaparser.symbolsolver;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class Issue2289Test extends AbstractSymbolResolutionTest {

    @Test
    public void test() {

        TypeSolver typeSolver = new ReflectionTypeSolver(false);
        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(typeSolver));
        StaticJavaParser.setConfiguration(config);

        String s = 
                "public class Test \n" + 
                "{\n" + 
                "    public class InnerClass \n" + 
                "    {\n" + 
                "        public InnerClass(int i, int j) {  \n" + 
                "        }\n" + 
                "\n" + 
                "        public InnerClass(int i, int ...j) {  \n" + 
                "        } \n" + 
                "    }\n" + 
                " \n" + 
                "    public Test() { \n" + 
                "        new InnerClass(1,2);\n" + 
                "        new InnerClass(1,2,3);\n" + 
                "    } \n" + 
                "}";
        
        CompilationUnit cu = StaticJavaParser.parse(s);
        List<ObjectCreationExpr> exprs = cu.findAll(ObjectCreationExpr .class);
        
        assertEquals("Test.InnerClass.InnerClass(int, int)", exprs.get(0).resolve().getQualifiedSignature());
        assertEquals("Test.InnerClass.InnerClass(int, int...)", exprs.get(1).resolve().getQualifiedSignature());

    }
    
}
