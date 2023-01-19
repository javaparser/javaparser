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
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

class Issue1456Test extends AbstractResolutionTest {

    @Test
    void fieldAccessIssue() throws IOException {
        Path rootSourceDir = adaptPath("src/test/resources/issue1456");
        Path pathToSourceFile = adaptPath(rootSourceDir.toString()+"/bar/A.java");
        
        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(new JavaParserTypeSolver(rootSourceDir.toFile())));
        StaticJavaParser.setConfiguration(config);
        
        CompilationUnit cu = StaticJavaParser.parse(pathToSourceFile);

        ClassOrInterfaceDeclaration cid = cu.findFirst(ClassOrInterfaceDeclaration.class).get();
        ResolvedTypeDeclaration rtd = cid.resolve();
        List<ResolvedReferenceType> ancestors = rtd.asClass().getAncestors();
        assertEquals("foo.A", ancestors.get(0).describe());
    }
}

