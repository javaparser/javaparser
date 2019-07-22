package com.github.javaparser.ast;

import com.github.javaparser.*;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import org.junit.jupiter.api.Test;

import java.io.IOException;

import static org.junit.jupiter.api.Assertions.*;

public class AncestorDescendantTests {

    @Test
    void nodeIsNotAncestorOfItself() throws IOException {
        JavaParser parser = new JavaParser();

        Provider provider = Providers.resourceProvider("com/github/javaparser/range/A.java");
        assertNotNull(provider);
        ParseResult<CompilationUnit> parse = parser.parse(ParseStart.COMPILATION_UNIT, provider);
        assertTrue(parse.isSuccessful());

        VariableDeclarationExpr node = parse.getResult().get()
                .getType(0) // class A
                .getMember(0).asMethodDeclaration() // method foo()
                .getBody().get().getStatement(0).asExpressionStmt() // int a = 42;
                .getExpression().asVariableDeclarationExpr(); // a = 42

        assertFalse(node.isAncestorOf(node));
    }

    @Test
    void nodeIsNotDescendantOfItself() throws IOException {
        JavaParser parser = new JavaParser();

        Provider provider = Providers.resourceProvider("com/github/javaparser/range/A.java");
        assertNotNull(provider);
        ParseResult<CompilationUnit> parse = parser.parse(ParseStart.COMPILATION_UNIT, provider);
        assertTrue(parse.isSuccessful());

        VariableDeclarationExpr node = parse.getResult().get()
                .getType(0) // class A
                .getMember(0).asMethodDeclaration() // method foo()
                .getBody().get().getStatement(0).asExpressionStmt() // int a = 42;
                .getExpression().asVariableDeclarationExpr(); // a = 42

        assertFalse(node.isDescendantOf(node));
    }

    @Test
    void nodeInSameFileIsDescendantOfAncestor() throws IOException {
        JavaParser parser = new JavaParser();

        Provider provider = Providers.resourceProvider("com/github/javaparser/range/A.java");
        assertNotNull(provider);
        ParseResult<CompilationUnit> parse = parser.parse(ParseStart.COMPILATION_UNIT, provider);
        assertTrue(parse.isSuccessful());

        VariableDeclarationExpr superNode = parse.getResult().get()
                .getType(0) // class A
                .getMember(0).asMethodDeclaration() // method foo()
                .getBody().get().getStatement(0).asExpressionStmt() // int a = 42;
                .getExpression().asVariableDeclarationExpr(); // a = 42

        Expression subNode = superNode.getVariable(0).getInitializer().get(); // 42

        assertTrue(superNode.isAncestorOf(subNode));
        assertFalse(subNode.isAncestorOf(superNode));
        assertTrue(subNode.isDescendantOf(superNode));
        assertFalse(superNode.isDescendantOf(subNode));
    }

    @Test
    void nodesInTwoDifferentFilesAreNotDescendantOrAncestorOfEachOther() throws IOException {
        JavaParser parser = new JavaParser();

        Provider providerA = Providers.resourceProvider("com/github/javaparser/range/A.java");
        assertNotNull(providerA);
        ParseResult<CompilationUnit> parseA = parser.parse(ParseStart.COMPILATION_UNIT, providerA);
        assertTrue(parseA.isSuccessful());

        Provider providerB = Providers.resourceProvider("com/github/javaparser/range/B.java");
        assertNotNull(providerB);
        ParseResult<CompilationUnit> parseB = parser.parse(ParseStart.COMPILATION_UNIT, providerB);
        assertTrue(parseB.isSuccessful());

        VariableDeclarationExpr superNodeA = parseA.getResult().get()
                .getType(0) // class A
                .getMember(0).asMethodDeclaration() // method foo()
                .getBody().get().getStatement(0).asExpressionStmt() // int a = 42;
                .getExpression().asVariableDeclarationExpr(); // a = 42

        Expression subNodeA = superNodeA.getVariable(0).getInitializer().get(); // 42

        VariableDeclarationExpr superNodeB = parseB.getResult().get()
                .getType(0) // class B
                .getMember(0).asMethodDeclaration() // method foo()
                .getBody().get().getStatement(0).asExpressionStmt() // int b = 42;
                .getExpression().asVariableDeclarationExpr(); // b = 42

        Expression subNodeB = superNodeB.getVariable(0).getInitializer().get(); // 42

        assertFalse(superNodeA.isAncestorOf(superNodeB));
        assertFalse(superNodeA.isDescendantOf(subNodeB));
        assertFalse(superNodeB.isAncestorOf(superNodeA));
        assertFalse(superNodeB.isDescendantOf(subNodeA));
    }
}
