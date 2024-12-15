/*
 * Copyright (C) 2013-2024 The JavaParser Team.
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

import com.github.javaparser.JavaParser;
import com.github.javaparser.JavaParserAdapter;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.ast.body.*;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import org.junit.jupiter.api.Test;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserFieldDeclaration;

public class Issue3674Test extends AbstractResolutionTest {

    @Test
    void test() {

        String code = "public class Class {\n" + "\n"
                + "        int attribute;\n"
                + "\n"
                + "        private int method() {\n"
                + "            int value = attribute;\n"
                + "            double attribute = 0.0;\n"
                + "            return (int) (attribute + 1);\n"
                + "        }\n"
                + "}";
        ParserConfiguration parserConfiguration =
                new ParserConfiguration().setSymbolResolver(symbolResolver(defaultTypeSolver()));

        CompilationUnit cu =
                JavaParserAdapter.of(new JavaParser(parserConfiguration)).parse(code);

        MethodDeclaration oce = cu.findFirst(MethodDeclaration.class).get();
        VariableDeclarationExpr decl = oce.findFirst(VariableDeclarationExpr.class).get();

        NameExpr nameAttributeExpr = oce.findFirst(NameExpr.class).get();
        ResolvedValueDeclaration res = nameAttributeExpr.resolve();
        assertTrue(res instanceof JavaParserFieldDeclaration);
        JavaParserFieldDeclaration resolvedFieldDeclaration = (JavaParserFieldDeclaration)res;
        assertEquals(resolvedFieldDeclaration.getName(),"attribute");
        assertEquals(resolvedFieldDeclaration.getType().describe(),"int");
        
    }
}
