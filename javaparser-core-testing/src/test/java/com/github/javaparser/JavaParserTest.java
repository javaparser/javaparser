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

import static com.github.javaparser.ParseStart.*;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.*;
import static com.github.javaparser.Providers.*;
import static com.github.javaparser.Range.*;
import static com.github.javaparser.StaticJavaParser.*;
import static com.github.javaparser.utils.CodeGenerationUtils.*;
import static com.github.javaparser.utils.TestUtils.*;
import static com.github.javaparser.utils.Utils.*;
import static org.junit.jupiter.api.Assertions.*;

import java.io.IOException;
import java.nio.file.Path;
import java.util.Optional;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.AnnotationMemberDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.ArrayCreationExpr;
import com.github.javaparser.ast.expr.CastExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ForStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.stmt.SwitchEntry;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.IntersectionType;
import com.github.javaparser.ast.type.Type;

class JavaParserTest {

    @BeforeEach
    void setToLatestJava() {
        StaticJavaParser.getConfiguration().setLanguageLevel(BLEEDING_EDGE);
    }

    @AfterEach
    void resetJavaLevel() {
        StaticJavaParser.getConfiguration().setLanguageLevel(CURRENT);
    }

    @Test
    void rangeOfAnnotationMemberDeclarationIsCorrect() {
        String code = "@interface AD { String foo(); }";
        CompilationUnit cu = parse(code);
        AnnotationMemberDeclaration memberDeclaration = cu.getAnnotationDeclarationByName("AD").get().getMember(0).asAnnotationMemberDeclaration();
        assertTrue(memberDeclaration.getRange().isPresent());
        assertEquals(new Range(new Position(1, 17), new Position(1, 29)), memberDeclaration.getRange().get());
    }

    @Test
    void testSourcePositionsWithUnicodeEscapes() {
        String code = "@interface AD \\u007B String foo(); \\u007D";
        CompilationUnit cu = parseWithUnicodeEscapes(code).getResult().get();
        AnnotationMemberDeclaration memberDeclaration = cu.getAnnotationDeclarationByName("AD").get().getMember(0).asAnnotationMemberDeclaration();
        assertTrue(memberDeclaration.getRange().isPresent());
        assertEquals(new Range(new Position(1, 22), new Position(1, 34)), memberDeclaration.getRange().get());
    }

    @Test
    void testSourcePositionsWithBrokenUnicodeEscapes() {
    	// Source positions
    	//                      111111111122222222 2 22333 3333
    	//             123456789012345678901234567 8 90123 4567
    	String code = "@interface AD { String X = \"\\uABC\"; }";
    	ParseResult<CompilationUnit> cu = parseWithUnicodeEscapes(code);
    	assertFalse(cu.getResult().isPresent());
    	assertEquals("Lexical error at line 1, column 34.  Encountered: \"\\\"\" (34), after : \"\\\"\\\\uABC\"", cu.getProblem(0).getMessage());
    }
    
	private static ParseResult<CompilationUnit> parseWithUnicodeEscapes(String code) {
		ParserConfiguration config = new ParserConfiguration();
        config.setPreprocessUnicodeEscapes(true);
		return new JavaParser(config).parse(code);
	}

    @Test
    void rangeOfAnnotationMemberDeclarationWithArrayTypeIsCorrect() {
        String code = "@interface AD { String[] foo(); }";
        CompilationUnit cu = parse(code);
        AnnotationMemberDeclaration memberDeclaration = cu.getAnnotationDeclarationByName("AD").get().getMember(0).asAnnotationMemberDeclaration();
        assertTrue(memberDeclaration.getRange().isPresent());
        assertEquals(new Range(new Position(1, 17), new Position(1, 31)), memberDeclaration.getRange().get());
    }

    @Test
    void rangeOfArrayCreationLevelWithExpressionIsCorrect() {
        String code = "new int[123][456]";
        ArrayCreationExpr expression = parseExpression(code);
        Optional<Range> range;

        range = expression.getLevels().get(0).getRange();
        assertTrue(range.isPresent());
        assertEquals(new Range(new Position(1, 8), new Position(1, 12)), range.get());

        range = expression.getLevels().get(1).getRange();
        assertTrue(range.isPresent());
        assertEquals(new Range(new Position(1, 13), new Position(1, 17)), range.get());
    }

    @Test
    void rangeOfArrayCreationLevelWithoutExpressionIsCorrect() {
        String code = "new int[][]";
        ArrayCreationExpr expression = parseExpression(code);
        Optional<Range> range;

        range = expression.getLevels().get(0).getRange();
        assertTrue(range.isPresent());
        assertEquals(new Range(new Position(1, 8), new Position(1, 9)), range.get());

        range = expression.getLevels().get(1).getRange();
        assertTrue(range.isPresent());
        assertEquals(new Range(new Position(1, 10), new Position(1, 11)), range.get());
    }

    @Test
    void parseErrorContainsLocation() {
        ParseResult<CompilationUnit> result = new JavaParser().parse(COMPILATION_UNIT, provider("class X { // blah"));

        Problem problem = result.getProblem(0);
        assertEquals(range(1, 9, 1, 17), problem.getLocation().get().toRange().get());
        assertEquals("Parse error. Found <EOF>, expected one of  \";\" \"<\" \"@\" \"abstract\" \"boolean\" \"byte\" \"char\" \"class\" \"default\" \"double\" \"enum\" \"exports\" \"final\" \"float\" \"int\" \"interface\" \"long\" \"module\" \"native\" \"open\" \"opens\" \"private\" \"protected\" \"provides\" \"public\" \"requires\" \"short\" \"static\" \"strictfp\" \"synchronized\" \"to\" \"transient\" \"transitive\" \"uses\" \"void\" \"volatile\" \"with\" \"{\" \"}\" <IDENTIFIER>", problem.getMessage());
        assertInstanceOf(ParseException.class, problem.getCause().get());
    }

    @Test
    void parseIntersectionType() {
        String code = "(Runnable & Serializable) (() -> {})";
        Expression expression = parseExpression(code);
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
    void rangeOfIntersectionType() {
        String code = "class A {" + EOL
                + "  Object f() {" + EOL
                + "    return (Comparator<Map.Entry<K, V>> & Serializable)(c1, c2) -> c1.getKey().compareTo(c2.getKey()); " + EOL
                + "}}";
        CompilationUnit cu = parse(code);
        MethodDeclaration methodDeclaration = cu.getClassByName("A").get().getMember(0).asMethodDeclaration();
        ReturnStmt returnStmt = methodDeclaration.getBody().get().getStatement(0).asReturnStmt();
        CastExpr castExpr = returnStmt.getExpression().get().asCastExpr();
        Type type = castExpr.getType();
        assertEquals(range(3, 13, 3, 54), type.getRange().get());
    }

    @Test
    void rangeOfCast() {
        String code = "class A {" + EOL
                + "  Object f() {" + EOL
                + "    return (Comparator<Map.Entry<K, V>> & Serializable)(c1, c2) -> c1.getKey().compareTo(c2.getKey()); " + EOL
                + "}}";
        CompilationUnit cu = parse(code);
        MethodDeclaration methodDeclaration = cu.getClassByName("A").get().getMember(0).asMethodDeclaration();
        ReturnStmt returnStmt = methodDeclaration.getBody().get().getStatement(0).asReturnStmt();
        CastExpr castExpr = returnStmt.getExpression().get().asCastExpr();
        assertEquals(range(3, 12, 3, 101), castExpr.getRange().get());
    }

    @Test
    void rangeOfCastNonIntersection() {
        String code = "class A {" + EOL
                + "  Object f() {" + EOL
                + "    return (Comparator<Map.Entry<K, V>>               )(c1, c2) -> c1.getKey().compareTo(c2.getKey()); " + EOL
                + "}}";
        CompilationUnit cu = parse(code);
        MethodDeclaration methodDeclaration = cu.getClassByName("A").get().getMember(0).asMethodDeclaration();
        ReturnStmt returnStmt = methodDeclaration.getBody().get().getStatement(0).asReturnStmt();
        CastExpr castExpr = returnStmt.getExpression().get().asCastExpr();
        assertEquals(range(3, 12, 3, 101), castExpr.getRange().get());
    }

    @Test
    void rangeOfLambda() {
        String code = "class A {" + EOL
                + "  Object f() {" + EOL
                + "    return (Comparator<Map.Entry<K, V>> & Serializable)(c1, c2) -> c1.getKey().compareTo(c2.getKey()); " + EOL
                + "}}";
        CompilationUnit cu = parse(code);
        MethodDeclaration methodDeclaration = cu.getClassByName("A").get().getMember(0).asMethodDeclaration();
        ReturnStmt returnStmt = methodDeclaration.getBody().get().getStatement(0).asReturnStmt();
        CastExpr castExpr = returnStmt.getExpression().get().asCastExpr();
        LambdaExpr lambdaExpr = castExpr.getExpression().asLambdaExpr();
        assertEquals(range(3, 56, 3, 101), lambdaExpr.getRange().get());
        assertEquals(GeneratedJavaParserConstants.LPAREN, lambdaExpr.getTokenRange().get().getBegin().getKind());
        assertEquals(GeneratedJavaParserConstants.RPAREN, lambdaExpr.getTokenRange().get().getEnd().getKind());
    }

    @Test
    void rangeOfLambdaBody() {
        String code = "class A {" + EOL
                + "  Object f() {" + EOL
                + "    return (Comparator<Map.Entry<K, V>> & Serializable)(c1, c2) -> c1.getKey().compareTo(c2.getKey()); " + EOL
                + "}}";
        CompilationUnit cu = parse(code);
        MethodDeclaration methodDeclaration = cu.getClassByName("A").get().getMember(0).asMethodDeclaration();
        ReturnStmt returnStmt = methodDeclaration.getBody().get().getStatement(0).asReturnStmt();
        CastExpr castExpr = returnStmt.getExpression().get().asCastExpr();
        LambdaExpr lambdaExpr = castExpr.getExpression().asLambdaExpr();
        Statement lambdaBody = lambdaExpr.getBody();
        assertEquals(range(3, 68, 3, 101), lambdaBody.getRange().get());
    }

    @Test
    void testNotStoringTokens() {
        JavaParser javaParser = new JavaParser(new ParserConfiguration().setStoreTokens(false));
        ParseResult<CompilationUnit> result = javaParser.parse(ParseStart.COMPILATION_UNIT, provider("class X{}"));
        assertFalse(result.getResult().get().getTokenRange().isPresent());
    }

    @Test
    void trailingCodeIsAnError() {
        assertThrows(ParseProblemException.class, () -> parseBlock("{} efijqoifjqefj"));
    }

    @Test
    void trailingWhitespaceIsIgnored() {
        BlockStmt blockStmt = parseBlock("{} // hello");
        assertEquals("{}", blockStmt.getTokenRange().get().toString());
    }

    @Test
    void everyTokenHasACategory() throws IOException {
        final int tokenCount = GeneratedJavaParserConstants.tokenImage.length;
        Path tokenTypesPath = mavenModuleRoot(JavaParserTest.class).resolve("../javaparser-core/src/main/java/com/github/javaparser/TokenTypes.java");
        CompilationUnit tokenTypesCu = parse(tokenTypesPath);
        // -1 to take off the default: case.
        int switchEntries = tokenTypesCu.findAll(SwitchEntry.class).size() - 1;
        // The amount of "case XXX:" in TokenTypes.java should be equal to the amount of tokens JavaCC knows about:
        assertEquals(tokenCount, switchEntries);
    }

    @Test
    void parsingInitializedAndUnitializedVarsInForStmt() {
        ForStmt forStmt = parseStatement("for(int a,b=0;;){}").asForStmt();
        assertEquals(1, forStmt.getInitialization().size());
        assertTrue(forStmt.getInitialization().get(0).isVariableDeclarationExpr());
        assertEquals(2, forStmt.getInitialization().get(0).asVariableDeclarationExpr().getVariables().size());
        assertEquals("a", forStmt.getInitialization().get(0).asVariableDeclarationExpr().getVariables().get(0).getNameAsString());
        assertEquals("b", forStmt.getInitialization().get(0).asVariableDeclarationExpr().getVariables().get(1).getNameAsString());
        assertFalse(forStmt.getInitialization().get(0).asVariableDeclarationExpr().getVariables().get(0).getInitializer().isPresent());
        assertTrue(forStmt.getInitialization().get(0).asVariableDeclarationExpr().getVariables().get(1).getInitializer().isPresent());
    }

    @Test
    void parsingInitializedAndUnitializedVarsInForStmtComplexCase() {
        // See issue 1281
        ForStmt forStmt = parseStatement("for(int i, j = array2.length - 1;;){}").asForStmt();
        assertEquals(1, forStmt.getInitialization().size());
        assertTrue(forStmt.getInitialization().get(0).isVariableDeclarationExpr());
        assertEquals(2, forStmt.getInitialization().get(0).asVariableDeclarationExpr().getVariables().size());
        assertEquals("i", forStmt.getInitialization().get(0).asVariableDeclarationExpr().getVariables().get(0).getNameAsString());
        assertEquals("j", forStmt.getInitialization().get(0).asVariableDeclarationExpr().getVariables().get(1).getNameAsString());
        assertFalse(forStmt.getInitialization().get(0).asVariableDeclarationExpr().getVariables().get(0).getInitializer().isPresent());
        assertTrue(forStmt.getInitialization().get(0).asVariableDeclarationExpr().getVariables().get(1).getInitializer().isPresent());
    }

    @Test
    void creatingNewObjectCreationExprShouldDefaultToParsing() {
        String className = String.class.getCanonicalName();
        ClassOrInterfaceType type = parseClassOrInterfaceType(className);
        ObjectCreationExpr expected = parseExpression("new " + className + "()");
        ObjectCreationExpr actual = new ObjectCreationExpr(null, type, NodeList.nodeList());
        assertEquals(expected, actual);
    }

    @Test
    void parseModuleDeclaration() {
        StaticJavaParser.parseModuleDeclaration("module X {}");
    }

    @Test
    void parseModuleDirective() {
        StaticJavaParser.parseModuleDirective("opens C;");
    }

    @Test
    void parseTypeParameter() {
        StaticJavaParser.parseTypeParameter("T extends Serializable & AttachableListener");
    }

    @Test
    void parseTypeDeclaration() {
        StaticJavaParser.parseTypeDeclaration("enum Z {A, B}");
    }
}
