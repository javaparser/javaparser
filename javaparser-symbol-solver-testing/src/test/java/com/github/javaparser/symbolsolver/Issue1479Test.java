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

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.resolution.declarations.ResolvedFieldDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class Issue1479Test extends AbstractSymbolResolutionTest {

    @Test
    public void test() throws IOException {
        
        CombinedTypeSolver typeSolver = new CombinedTypeSolver(new ReflectionTypeSolver(), new JavaParserTypeSolver(adaptPath("src/test/resources/issue1479")));
        JavaSymbolSolver symbolSolver = new JavaSymbolSolver(typeSolver);
        StaticJavaParser.getConfiguration().setSymbolResolver(symbolSolver);
        
        String src = 
                "public class Foo {\n" +
                "  public void m() {\n" +
                "    doSomething(B.AFIELD);\n" +
                "  }\n" +
                "  public void doSomething(String a) {\n" +
                "  }\n" +
                "}\n";

        CompilationUnit cu = StaticJavaParser.parse(src);
        FieldAccessExpr fae = cu.findFirst(FieldAccessExpr.class).get();
        assertTrue(fae.calculateResolvedType().describe().equals("java.lang.String"));
        ResolvedFieldDeclaration value = fae.resolve().asField();
        assertTrue(value.getName().equals("AFIELD"));
        Optional<FieldDeclaration> fd = value.toAst(FieldDeclaration.class);
        assertEquals("a", fd.get().getVariable(0).getInitializer().get().asStringLiteralExpr().getValue());
    }
    
}
