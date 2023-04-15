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

package com.github.javaparser.issues;

import com.github.javaparser.Range;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.MethodDeclaration;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

import java.io.IOException;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class Issue2627Test {

    private static final String RESOURCE_PATH_STRING_CR = "com/github/javaparser/issue_samples/issue_2627/Ops_cr.java";
    private static final String RESOURCE_PATH_STRING_LF = "com/github/javaparser/issue_samples/issue_2627/Ops_lf.java";
    private static final String RESOURCE_PATH_STRING_CRLF = "com/github/javaparser/issue_samples/issue_2627/Ops_crlf.java";
    private static final String RESOURCE_PATH_STRING_MINIMAL = "com/github/javaparser/issue_samples/issue_2627/Ops_minimal.java";
    private static final String RESOURCE_PATH_STRING_ORIGINAL = "com/github/javaparser/issue_samples/issue_2627/Ops.java";
    private static final String RESOURCE_PATH_GROOVY_ORIGINAL = "com/github/javaparser/issue_samples/issue_2627/DefaultStrategy.java";

    private static Stream<Arguments> arguments_minimal() {
        return Stream.of(
                Arguments.of("methodA", 258, 260),
                Arguments.of("methodB", 163, 164),
                Arguments.of("methodC", 3, 4)
        );
    }

    private static Stream<Arguments> arguments_original() {
        return Stream.of(
                Arguments.of("batchToSpace", 796, 799),
                Arguments.of("batchToSpaceNd", 911, 914),
                Arguments.of("placeholder", 3686, 3689)
        );
    }

    private static Stream<Arguments> arguments_groovy_original() {
        return Stream.of(
                Arguments.of("buildMethod", 180, 193)
        );
    }

    private void assertMethodInExpectedLines(CompilationUnit cu, String name, int expectedStartLine, int expectedEndLine) {
        MethodDeclaration node = getFirstMethodDeclarationByName(cu, name);
        assertNodeInExpectedLines(node, expectedStartLine, expectedEndLine);
    }

    private void assertNodeInExpectedLines(Node node, int expectedStartLine, int expectedEndLine) {
        Range range = node.getRange().get();

        assertEquals(expectedStartLine, range.begin.line);
        assertEquals(expectedEndLine, range.end.line);
    }

    private MethodDeclaration getFirstMethodDeclarationByName(CompilationUnit cu, String name) {
        return cu.findAll(MethodDeclaration.class).stream()
                .filter(n -> name.equals(n.getNameAsString()))
                .findFirst()
                .get();
    }

//    @Test
//    public void cuLength_minimal() throws IOException {
//        CompilationUnit cu = StaticJavaParser.parseResource(RESOURCE_PATH_STRING_MINIMAL);
//
//        final Range cuRange = cu.getRange().get();
//
//        int lineCount = cuRange.end.line - cuRange.begin.line;
//
//    }

//    @Test
//    public void commentPositions_minimal() throws IOException {
//        CompilationUnit cu = StaticJavaParser.parseResource(RESOURCE_PATH_STRING_MINIMAL);
//
//        List<Comment> allComments = cu.getAllComments();
//        for (int i = 0; i < allComments.size(); i++) {
//            Comment comment = allComments.get(i);
//            Optional<Range> optionalRange = comment.getRange();
//            if (optionalRange.isPresent()) {
//                Range range = optionalRange.get();
//                final TokenRange tokens = comment.getTokenRange().get();
//                int tokenIndex = 0;
//                for (JavaToken token : tokens) {
//                    System.out.println("token " + tokenIndex + " = " + token);
//                    tokenIndex++;
//                }
//                System.out.println(tokens);
//            }
//        }
//
//
////        assertNodeInExpectedLines(cu, 1, 288);
//    }

    @ParameterizedTest
    @MethodSource("arguments_minimal")
    public void method_minimal(String name, int expectedStart, int expectedEnd) throws IOException {
        CompilationUnit cu = StaticJavaParser.parseResource(RESOURCE_PATH_STRING_MINIMAL);
        assertMethodInExpectedLines(cu, name, expectedStart, expectedEnd);
    }


    @ParameterizedTest
    @MethodSource("arguments_original")
    public void method_original(String name, int expectedStart, int expectedEnd) throws IOException {
        CompilationUnit cu = StaticJavaParser.parseResource(RESOURCE_PATH_STRING_ORIGINAL);
        assertMethodInExpectedLines(cu, name, expectedStart, expectedEnd);
    }

    @ParameterizedTest
    @MethodSource("arguments_original")
    public void method_original_cr(String name, int expectedStart, int expectedEnd) throws IOException {
        CompilationUnit cu = StaticJavaParser.parseResource(RESOURCE_PATH_STRING_CR);
        assertMethodInExpectedLines(cu, name, expectedStart, expectedEnd);
    }

    @ParameterizedTest
    @MethodSource("arguments_original")
    public void method_original_crlf(String name, int expectedStart, int expectedEnd) throws IOException {
        CompilationUnit cu = StaticJavaParser.parseResource(RESOURCE_PATH_STRING_CRLF);
        assertMethodInExpectedLines(cu, name, expectedStart, expectedEnd);
    }

    @ParameterizedTest
    @MethodSource("arguments_original")
    public void method_original_lf(String name, int expectedStart, int expectedEnd) throws IOException {
        CompilationUnit cu = StaticJavaParser.parseResource(RESOURCE_PATH_STRING_LF);
        assertMethodInExpectedLines(cu, name, expectedStart, expectedEnd);
    }


    @ParameterizedTest
    @MethodSource("arguments_groovy_original")
    public void method_groovy_original(String name, int expectedStart, int expectedEnd) throws IOException {
        CompilationUnit cu = StaticJavaParser.parseResource(RESOURCE_PATH_GROOVY_ORIGINAL);
        assertMethodInExpectedLines(cu, name, expectedStart, expectedEnd);
    }

}
