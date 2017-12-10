/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
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

package com.github.javaparser;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.AnnotationMemberDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.ArrayCreationExpr;
import com.github.javaparser.ast.expr.CastExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.IntersectionType;
import com.github.javaparser.ast.type.Type;
import org.junit.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.util.Optional;

import static com.github.javaparser.ParseStart.COMPILATION_UNIT;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.Range.range;
import static com.github.javaparser.utils.CodeGenerationUtils.mavenModuleRoot;
import static com.github.javaparser.utils.TestUtils.assertInstanceOf;
import static com.github.javaparser.utils.Utils.EOL;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class JavaParserTest {

    @Test
    public void rangeOfAnnotationMemberDeclarationIsCorrect() {
        String code = "@interface AD { String foo(); }";
        CompilationUnit cu = JavaParser.parse(code);
        AnnotationMemberDeclaration memberDeclaration = cu.getAnnotationDeclarationByName("AD").get().getMember(0).asAnnotationMemberDeclaration();
        assertEquals(true, memberDeclaration.getRange().isPresent());
        assertEquals(new Range(new Position(1, 17), new Position(1, 29)), memberDeclaration.getRange().get());
    }

    @Test
    public void rangeOfAnnotationMemberDeclarationWithArrayTypeIsCorrect() {
        String code = "@interface AD { String[] foo(); }";
        CompilationUnit cu = JavaParser.parse(code);
        AnnotationMemberDeclaration memberDeclaration = cu.getAnnotationDeclarationByName("AD").get().getMember(0).asAnnotationMemberDeclaration();
        assertEquals(true, memberDeclaration.getRange().isPresent());
        assertEquals(new Range(new Position(1, 17), new Position(1, 31)), memberDeclaration.getRange().get());
    }

    @Test
    public void rangeOfArrayCreationLevelWithExpressionIsCorrect() {
        String code = "new int[123][456]";
        ArrayCreationExpr expression = JavaParser.parseExpression(code);
        Optional<Range> range;

        range = expression.getLevels().get(0).getRange();
        assertEquals(true, range.isPresent());
        assertEquals(new Range(new Position(1, 8), new Position(1, 12)), range.get());

        range = expression.getLevels().get(1).getRange();
        assertEquals(true, range.isPresent());
        assertEquals(new Range(new Position(1, 13), new Position(1, 17)), range.get());
    }

    @Test
    public void rangeOfArrayCreationLevelWithoutExpressionIsCorrect() {
        String code = "new int[][]";
        ArrayCreationExpr expression = JavaParser.parseExpression(code);
        Optional<Range> range;

        range = expression.getLevels().get(0).getRange();
        assertEquals(true, range.isPresent());
        assertEquals(new Range(new Position(1, 8), new Position(1, 9)), range.get());

        range = expression.getLevels().get(1).getRange();
        assertEquals(true, range.isPresent());
        assertEquals(new Range(new Position(1, 10), new Position(1, 11)), range.get());
    }

    @Test
    public void parseErrorContainsLocation() {
        ParseResult<CompilationUnit> result = new JavaParser().parse(COMPILATION_UNIT, provider("class X { // blah"));

        Problem problem = result.getProblem(0);
        assertEquals(range(1, 9, 1, 17), problem.getLocation().get().toRange().get());
        assertEquals("Parse error. Found <EOF>, expected one of  \";\" \"<\" \"@\" \"abstract\" \"boolean\" \"byte\" \"char\" \"class\" \"default\" \"double\" \"enum\" \"exports\" \"final\" \"float\" \"int\" \"interface\" \"long\" \"module\" \"native\" \"open\" \"opens\" \"private\" \"protected\" \"provides\" \"public\" \"requires\" \"short\" \"static\" \"strictfp\" \"synchronized\" \"to\" \"transient\" \"transitive\" \"uses\" \"void\" \"volatile\" \"with\" \"{\" \"}\" <IDENTIFIER>", problem.getMessage());
        assertInstanceOf(ParseException.class, problem.getCause().get());
    }

    @Test
    public void parseIntersectionType() {
        String code = "(Runnable & Serializable) (() -> {})";
        Expression expression = JavaParser.parseExpression(code);
        Type type = expression.asCastExpr().getType();

        assertTrue(type instanceof IntersectionType);
        IntersectionType intersectionType = type.asIntersectionType();
        assertEquals(2, intersectionType.getElements().size());
        assertTrue(intersectionType.getElements().get(0) instanceof ClassOrInterfaceType);
        assertEquals("Runnable", intersectionType.getElements().get(0).asClassOrInterfaceType().getNameAsString());
        assertTrue(intersectionType.getElements().get(1) instanceof ClassOrInterfaceType);
        assertEquals("Serializable", intersectionType.getElements().get(1).asClassOrInterfaceType().getNameAsString());
    }

    @Test
    public void rangeOfIntersectionType() {
        String code = "class A {" + EOL
                + "  Object f() {" + EOL
                + "    return (Comparator<Map.Entry<K, V>> & Serializable)(c1, c2) -> c1.getKey().compareTo(c2.getKey()); " + EOL
                + "}}";
        CompilationUnit cu = JavaParser.parse(code);
        MethodDeclaration methodDeclaration = cu.getClassByName("A").get().getMember(0).asMethodDeclaration();
        ReturnStmt returnStmt = methodDeclaration.getBody().get().getStatement(0).asReturnStmt();
        CastExpr castExpr = returnStmt.getExpression().get().asCastExpr();
        Type type = castExpr.getType();
        assertEquals(range(3, 13, 3, 54), type.getRange().get());
    }

    @Test
    public void rangeOfCast() {
        String code = "class A {" + EOL
                + "  Object f() {" + EOL
                + "    return (Comparator<Map.Entry<K, V>> & Serializable)(c1, c2) -> c1.getKey().compareTo(c2.getKey()); " + EOL
                + "}}";
        CompilationUnit cu = JavaParser.parse(code);
        MethodDeclaration methodDeclaration = cu.getClassByName("A").get().getMember(0).asMethodDeclaration();
        ReturnStmt returnStmt = methodDeclaration.getBody().get().getStatement(0).asReturnStmt();
        CastExpr castExpr = returnStmt.getExpression().get().asCastExpr();
        assertEquals(range(3, 12, 3, 101), castExpr.getRange().get());
    }

    @Test
    public void rangeOfCastNonIntersection() {
        String code = "class A {" + EOL
                + "  Object f() {" + EOL
                + "    return (Comparator<Map.Entry<K, V>>               )(c1, c2) -> c1.getKey().compareTo(c2.getKey()); " + EOL
                + "}}";
        CompilationUnit cu = JavaParser.parse(code);
        MethodDeclaration methodDeclaration = cu.getClassByName("A").get().getMember(0).asMethodDeclaration();
        ReturnStmt returnStmt = methodDeclaration.getBody().get().getStatement(0).asReturnStmt();
        CastExpr castExpr = returnStmt.getExpression().get().asCastExpr();
        assertEquals(range(3, 12, 3, 101), castExpr.getRange().get());
    }

    @Test
    public void rangeOfLambda() {
        String code = "class A {" + EOL
                + "  Object f() {" + EOL
                + "    return (Comparator<Map.Entry<K, V>> & Serializable)(c1, c2) -> c1.getKey().compareTo(c2.getKey()); " + EOL
                + "}}";
        CompilationUnit cu = JavaParser.parse(code);
        MethodDeclaration methodDeclaration = cu.getClassByName("A").get().getMember(0).asMethodDeclaration();
        ReturnStmt returnStmt = methodDeclaration.getBody().get().getStatement(0).asReturnStmt();
        CastExpr castExpr = returnStmt.getExpression().get().asCastExpr();
        LambdaExpr lambdaExpr = castExpr.getExpression().asLambdaExpr();
        assertEquals(range(3, 56, 3, 101), lambdaExpr.getRange().get());
        assertEquals(GeneratedJavaParserConstants.LPAREN, lambdaExpr.getTokenRange().get().getBegin().getKind());
        assertEquals(GeneratedJavaParserConstants.RPAREN, lambdaExpr.getTokenRange().get().getEnd().getKind());
    }

    @Test
    public void rangeOfLambdaBody() {
        String code = "class A {" + EOL
                + "  Object f() {" + EOL
                + "    return (Comparator<Map.Entry<K, V>> & Serializable)(c1, c2) -> c1.getKey().compareTo(c2.getKey()); " + EOL
                + "}}";
        CompilationUnit cu = JavaParser.parse(code);
        MethodDeclaration methodDeclaration = cu.getClassByName("A").get().getMember(0).asMethodDeclaration();
        ReturnStmt returnStmt = methodDeclaration.getBody().get().getStatement(0).asReturnStmt();
        CastExpr castExpr = returnStmt.getExpression().get().asCastExpr();
        LambdaExpr lambdaExpr = castExpr.getExpression().asLambdaExpr();
        Statement lambdaBody = lambdaExpr.getBody();
        assertEquals(range(3, 68, 3, 101), lambdaBody.getRange().get());
    }

    @Test
    public void testNotStoringTokens() {
        JavaParser javaParser = new JavaParser(new ParserConfiguration().setStoreTokens(false));
        ParseResult<CompilationUnit> result = javaParser.parse(ParseStart.COMPILATION_UNIT, provider("class X{}"));
        assertEquals(false, result.getTokens().isPresent());
    }

    @Test(expected = ParseProblemException.class)
    public void trailingCodeIsAnError() {
        JavaParser.parseBlock("{} efijqoifjqefj");
    }

    @Test
    public void trailingWhitespaceIsIgnored() {
        BlockStmt blockStmt = JavaParser.parseBlock("{} // hello");
        assertEquals("{}", blockStmt.getTokenRange().get().toString());
    }

    @Test
    public void everyTokenHasACategory() throws IOException {
        final int tokenCount = GeneratedJavaParserConstants.tokenImage.length;
        Path tokenTypesPath = mavenModuleRoot(JavaParserTest.class).resolve("../javaparser-core/src/main/java/com/github/javaparser/TokenTypes.java");
        CompilationUnit tokenTypesCu = JavaParser.parse(tokenTypesPath);
        // -1 to take off the default: case.
        int switchEntries = tokenTypesCu.findAll(SwitchEntryStmt.class).size()-1;
        // The amount of "case XXX:" in TokenTypes.java should be equal to the amount of tokens JavaCC knows about:
        assertEquals(tokenCount, switchEntries);
    }

    @Test
    public void parsingInitializedAndUnitializedVarsInForStmt() {
        ForStmt forStmt = JavaParser.parseStatement("for(int a,b=0;;){}").asForStmt();
        assertEquals(1, forStmt.getInitialization().size());
        assertEquals(true, forStmt.getInitialization().get(0).isVariableDeclarationExpr());
        assertEquals(2, forStmt.getInitialization().get(0).asVariableDeclarationExpr().getVariables().size());
        assertEquals("a", forStmt.getInitialization().get(0).asVariableDeclarationExpr().getVariables().get(0).getNameAsString());
        assertEquals("b", forStmt.getInitialization().get(0).asVariableDeclarationExpr().getVariables().get(1).getNameAsString());
        assertEquals(false, forStmt.getInitialization().get(0).asVariableDeclarationExpr().getVariables().get(0).getInitializer().isPresent());
        assertEquals(true, forStmt.getInitialization().get(0).asVariableDeclarationExpr().getVariables().get(1).getInitializer().isPresent());
    }

    @Test
    public void parsingInitializedAndUnitializedVarsInForStmtComplexCase() {
        // See issue 1281
        ForStmt forStmt = JavaParser.parseStatement("for(int i, j = array2.length - 1;;){}").asForStmt();
        assertEquals(1, forStmt.getInitialization().size());
        assertEquals(true, forStmt.getInitialization().get(0).isVariableDeclarationExpr());
        assertEquals(2, forStmt.getInitialization().get(0).asVariableDeclarationExpr().getVariables().size());
        assertEquals("i", forStmt.getInitialization().get(0).asVariableDeclarationExpr().getVariables().get(0).getNameAsString());
        assertEquals("j", forStmt.getInitialization().get(0).asVariableDeclarationExpr().getVariables().get(1).getNameAsString());
        assertEquals(false, forStmt.getInitialization().get(0).asVariableDeclarationExpr().getVariables().get(0).getInitializer().isPresent());
        assertEquals(true, forStmt.getInitialization().get(0).asVariableDeclarationExpr().getVariables().get(1).getInitializer().isPresent());
    }
}
