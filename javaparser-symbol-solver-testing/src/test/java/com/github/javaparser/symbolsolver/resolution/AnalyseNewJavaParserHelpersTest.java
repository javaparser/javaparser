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

package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.github.javaparser.symbolsolver.utils.LeanParserConfiguration;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * We analize a more recent version of JavaParser, after the project moved to Java 8.
 */
class AnalyseNewJavaParserHelpersTest extends AbstractResolutionTest {

    private static final Path src = adaptPath("src/test/test_sourcecode/javaparser_new_src/javaparser-core");

    private static TypeSolver TYPESOLVER = typeSolver();

    private static TypeSolver typeSolver() {
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
        combinedTypeSolver.add(new ReflectionTypeSolver());
        combinedTypeSolver.add(new JavaParserTypeSolver(src, new LeanParserConfiguration()));
        combinedTypeSolver.add(new JavaParserTypeSolver(adaptPath("src/test/test_sourcecode/javaparser_new_src/javaparser-generated-sources"), new LeanParserConfiguration()));
        return combinedTypeSolver;
    }

    private CompilationUnit parse(String fileName) throws IOException {
        Path sourceFile = src.resolve(fileName + ".java");
        return StaticJavaParser.parse(sourceFile);
    }

//    @Test
//    public void o1TypeIsCorrect() throws IOException, ParseException {
//        CompilationUnit cu = parse("com/github/javaparser/utils/PositionUtils");
//        NameExpr o1 = Navigator.findAllNodesOfGivenClass(cu, NameExpr.class).stream().filter(it -> it.getName()!=null && it.getName().equals("o1")).findFirst().get();
//        System.out.println(JavaParserFacade.get(TYPESOLVER).solve(o1).getCorrespondingDeclaration().getType());
//    }
//
//    @Test
//    public void o2TypeIsCorrect() throws IOException, ParseException {
//        CompilationUnit cu = parse("com/github/javaparser/utils/PositionUtils");
//        NameExpr o2 = Navigator.findAllNodesOfGivenClass(cu, NameExpr.class).stream().filter(it -> it.getName()!=null && it.getName().equals("o2")).findFirst().get();
//        System.out.println(JavaParserFacade.get(TYPESOLVER).solve(o2).getCorrespondingDeclaration().getType());
//    }
//
//    // To calculate the type of o1 and o2 I need to first calculate the type of the lambda
//    @Test
//    public void lambdaTypeIsCorrect() throws IOException, ParseException {
//        CompilationUnit cu = parse("com/github/javaparser/utils/PositionUtils");
//        LambdaExpr lambda = Navigator.findAllNodesOfGivenClass(cu, LambdaExpr.class).stream().filter(it -> it.getRange().begin.line == 50).findFirst().get();
//        System.out.println(JavaParserFacade.get(TYPESOLVER).getType(lambda));
//    }

    @Test
    void nodesTypeIsCorrect() throws IOException {
        CompilationUnit cu = parse("com/github/javaparser/utils/PositionUtils");
        NameExpr nodes = cu.findAll(NameExpr.class).stream().filter(it -> it.getName() != null && it.getName().getId().equals("nodes")).findFirst().get();
        ResolvedType type = JavaParserFacade.get(TYPESOLVER).solve(nodes).getCorrespondingDeclaration().getType();
        assertEquals("java.util.List<T>", type.describe());
        assertEquals(1, type.asReferenceType().typeParametersValues().size());
        assertEquals(true, type.asReferenceType().typeParametersValues().get(0).isTypeVariable());
        assertEquals("T", type.asReferenceType().typeParametersValues().get(0).asTypeParameter().getName());
        assertEquals("com.github.javaparser.utils.PositionUtils.sortByBeginPosition(java.util.List<T>).T", type.asReferenceType().typeParametersValues().get(0).asTypeParameter().getQualifiedName());
        assertEquals(1, type.asReferenceType().typeParametersValues().get(0).asTypeParameter().getBounds().size());
        ResolvedTypeParameterDeclaration.Bound bound = type.asReferenceType().typeParametersValues().get(0).asTypeParameter().getBounds().get(0);
        assertEquals(true, bound.isExtends());
        assertEquals("com.github.javaparser.ast.Node", bound.getType().describe());
    }

}
