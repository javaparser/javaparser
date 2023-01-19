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

package com.github.javaparser.symbolsolver;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

class Issue2878Test extends AbstractResolutionTest {

    @Test()
    void test() throws IOException {
        Path rootSourceDir = adaptPath("src/test/resources/issue2878");

        String src =
                "import java.util.Optional;\n" + 
                "\n" + 
                "public class U10 {\n" + 
                "    private final String file;\n" + 
                "\n" + 
                "    public U10(String file) {\n" + 
                "        this.file = file;\n" + 
                "    }\n" + 
                "    public void main(String[] args) {\n" + 
                "        U9 u1 = new U9(Optional.empty(), Optional.empty(), 1); // failed\n" + 
                "        U9 u2 = new U9(Optional.of(file), Optional.empty(), 1); // success\n" + 
                "        U9 u3 = new U9(Optional.empty(), Optional.empty(), \"/\"); // success\n" + 
                "        U9 u4 = new U9(Optional.empty(), Optional.empty(), true); // success\n" + 
                "    }\n" + 
                "}";
        
        ParserConfiguration config = new ParserConfiguration();
        CombinedTypeSolver cts = new CombinedTypeSolver(new ReflectionTypeSolver(false),new JavaParserTypeSolver(rootSourceDir.toFile()));
        config.setSymbolResolver(new JavaSymbolSolver(cts));
        StaticJavaParser.setConfiguration(config);

        CompilationUnit cu = StaticJavaParser.parse(src);

        List<ObjectCreationExpr> oces = cu.findAll(ObjectCreationExpr.class);

        assertEquals("U9.U9(java.util.Optional<java.lang.String>, java.util.Optional<U9>, int)", oces.get(0).resolve().getQualifiedSignature());
        assertEquals("U9.U9(java.util.Optional<java.lang.String>, java.util.Optional<U9>, int)", oces.get(1).resolve().getQualifiedSignature());
        assertEquals("U9.U9(java.util.Optional<java.lang.String>, java.util.Optional<java.lang.String>, java.lang.String)", oces.get(2).resolve().getQualifiedSignature());
        assertEquals("U9.U9(java.util.Optional<U9>, java.util.Optional<U9>, boolean)", oces.get(3).resolve().getQualifiedSignature());
    }
}
