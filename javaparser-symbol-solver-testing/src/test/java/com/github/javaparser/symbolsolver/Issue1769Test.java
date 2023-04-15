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
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class Issue1769Test extends AbstractResolutionTest {

    @Test()
    void testExtendsNestedclass() throws IOException {
        Path rootSourceDir = adaptPath("src/test/resources/issue1769");
        
        String src =
                "import foo.OtherClass;\n" +
                "public class MyClass extends OtherClass.InnerClass {\n" +
                "}\n";

        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(new JavaParserTypeSolver(rootSourceDir.toFile())));
        StaticJavaParser.setConfiguration(config);

        CompilationUnit cu = StaticJavaParser.parse(src);
        
        ClassOrInterfaceDeclaration cid = cu.findFirst(ClassOrInterfaceDeclaration.class).get();
        cid.getExtendedTypes().forEach(t-> {
            assertEquals("foo.OtherClass.InnerClass", t.resolve().describe());
        });

    }
    
    @Test()
    void testInstanciateNestedClass() throws IOException {
        Path rootSourceDir = adaptPath("src/test/resources/issue1769");
        
        String src =
                "import foo.OtherClass;\n" +
                "public class MyClass{\n" +
                "  public InnerClass myTest() {\n" + 
                "    return new OtherClass.InnerClass();\n" + 
                "  }\n" +
                "}\n";

        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(new JavaParserTypeSolver(rootSourceDir.toFile())));
        StaticJavaParser.setConfiguration(config);

        CompilationUnit cu = StaticJavaParser.parse(src);
        
        ObjectCreationExpr oce = cu.findFirst(ObjectCreationExpr.class).get();
        assertEquals("foo.OtherClass.InnerClass", oce.calculateResolvedType().asReferenceType().getQualifiedName());
        // The qualified name of the method composed by the qualfied name of the declaring type
        // followed by a dot and the name of the method.
        assertEquals("foo.OtherClass.InnerClass.InnerClass", oce.resolve().getQualifiedName());
    }
}
