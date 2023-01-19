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

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.MethodContext;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.github.javaparser.symbolsolver.utils.LeanParserConfiguration;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.List;

import static com.github.javaparser.StaticJavaParser.parse;

class Issue276Test extends AbstractResolutionTest{

    @Test
    void testSolveStaticallyImportedMemberType() throws IOException {
        CompilationUnit cu = parse(adaptPath("src/test/resources/issue276/foo/C.java"));
        ClassOrInterfaceDeclaration cls = Navigator.demandClassOrInterface(cu, "C");
        TypeSolver typeSolver = new CombinedTypeSolver(
        		new ReflectionTypeSolver(), 
        		new JavaParserTypeSolver(adaptPath("src/test/resources/issue276"), new LeanParserConfiguration()));
        List<MethodDeclaration> methods = cls.findAll(MethodDeclaration.class);
        boolean isSolved = false;
        for (MethodDeclaration method: methods) {
        	if (method.getNameAsString().equals("overrideMe")) {
        		MethodContext context = new MethodContext(method, typeSolver);
        		isSolved = context.solveType("FindMeIfYouCan").isSolved();
        	}
        }
        Assertions.assertTrue(isSolved);
    }
}
