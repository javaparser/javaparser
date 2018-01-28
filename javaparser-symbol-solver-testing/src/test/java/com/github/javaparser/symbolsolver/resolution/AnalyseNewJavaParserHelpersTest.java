/*
 * Copyright 2016 Federico Tomassetti
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.Test;

import java.io.File;
import java.io.IOException;

import static org.junit.Assert.assertEquals;

/**
 * We analize a more recent version of JavaParser, after the project moved to Java 8.
 */
public class AnalyseNewJavaParserHelpersTest extends AbstractResolutionTest {

    private static final File src = adaptPath(new File("src/test/test_sourcecode/javaparser_new_src/javaparser-core"));

    private static TypeSolver TYPESOLVER = typeSolver();

    private static TypeSolver typeSolver() {
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
        combinedTypeSolver.add(new ReflectionTypeSolver());
        combinedTypeSolver.add(new JavaParserTypeSolver(src));
        combinedTypeSolver.add(new JavaParserTypeSolver(adaptPath(new File("src/test/test_sourcecode/javaparser_new_src/javaparser-generated-sources"))));
        return combinedTypeSolver;
    }

    private CompilationUnit parse(String fileName) throws IOException {
        File sourceFile = new File(src.getAbsolutePath() + "/" + fileName + ".java");
        return JavaParser.parse(sourceFile);
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
    public void nodesTypeIsCorrect() throws IOException {
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
