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
import com.github.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

class Issue2360 extends AbstractSymbolResolutionTest {

    @Test
    void testUnaryExprResolvedViaUnaryNumericPromotion_char() {
        String source = "public class Test\n" + 
                "{\n" + 
                "   public class InnerClass\n" + 
                "   {\n" + 
                "       public InnerClass(char c) {}\n" + 
                "       public InnerClass(int i) {}\n" + 
                "   }\n" + 
                "    \n" + 
                "   public Test() {\n" + 
                "     new InnerClass(+'.'); \n" + 
                "   }\n" + 
                "}";
        
        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver(false)));
        StaticJavaParser.setConfiguration(config);

        CompilationUnit cu = StaticJavaParser.parse(source);
        ObjectCreationExpr expr = cu.findFirst(ObjectCreationExpr.class).get();
        ResolvedConstructorDeclaration rcd = expr.resolve();
        assertEquals("InnerClass(int)", rcd.getSignature());
    }
    
    @Test
    void testUnaryExprResolvedViaUnaryNumericPromotion_byte() {
        String source = "public class Test\n" + 
                "{\n" + 
                "   public class InnerClass\n" + 
                "   {\n" + 
                "       public InnerClass(char c) {}\n" + 
                "       public InnerClass(int i) {}\n" + 
                "   }\n" + 
                "    \n" + 
                "   public Test() {\n" + 
                "     byte b = 0;\n" +
                "     new InnerClass(+b); \n" + 
                "   }\n" + 
                "}";
        
        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver(false)));
        StaticJavaParser.setConfiguration(config);

        CompilationUnit cu = StaticJavaParser.parse(source);
        ObjectCreationExpr expr = cu.findFirst(ObjectCreationExpr.class).get();
        ResolvedConstructorDeclaration rcd = expr.resolve();
        assertEquals("InnerClass(int)", rcd.getSignature());
    }
    
    @Test
    void testUnaryExprResolvedViaUnaryNumericPromotion_short() {
        String source = "public class Test\n" + 
                "{\n" + 
                "   public class InnerClass\n" + 
                "   {\n" + 
                "       public InnerClass(char c) {}\n" + 
                "       public InnerClass(int i) {}\n" + 
                "   }\n" + 
                "    \n" + 
                "   public Test() {\n" + 
                "     short b = 0;\n" +
                "     new InnerClass(+b); \n" + 
                "   }\n" + 
                "}";
        
        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver(false)));
        StaticJavaParser.setConfiguration(config);

        CompilationUnit cu = StaticJavaParser.parse(source);
        ObjectCreationExpr expr = cu.findFirst(ObjectCreationExpr.class).get();
        ResolvedConstructorDeclaration rcd = expr.resolve();
        assertEquals("InnerClass(int)", rcd.getSignature());
    }
    
}
