package com.github.javaparser.ast.stmt;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParseStart;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.ParserConfiguration.LanguageLevel.*;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.TestUtils.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

class TryStmtTest {
    @Test
    void simpleTest() {
        TryStmt tryStmt = parse9("try(Reader x = new FileReader()){}");
        assertInstanceOf(VariableDeclarationExpr.class, tryStmt.getResources().get(0));
    }

    @Test
    void multipleTest() {
        TryStmt tryStmt = parse9("try(Reader x = new FileReader(); Reader x = new FileReader()){}");
        assertInstanceOf(VariableDeclarationExpr.class, tryStmt.getResources().get(0));

    }

    @Test
    void modifiersTest() {
        TryStmt tryStmt = parse9("try(final @A Reader x = new FileReader()){}");
        assertInstanceOf(VariableDeclarationExpr.class, tryStmt.getResources().get(0));

    }

    @Test
    void simpleVariable() {
        TryStmt tryStmt = parse9("try(a){}");
        assertInstanceOf(NameExpr.class, tryStmt.getResources().get(0));

    }

    @Test
    void twoSimpleVariables() {
        TryStmt tryStmt = parse9("try(a;b){}");
        assertInstanceOf(NameExpr.class, tryStmt.getResources().get(0));
        assertInstanceOf(NameExpr.class, tryStmt.getResources().get(1));

    }

    @Test
    void complexVariable() {
        TryStmt tryStmt = parse9("try(a.b.c){}");
        assertInstanceOf(FieldAccessExpr.class, tryStmt.getResources().get(0));

    }

    @Test
    void superAccess() {
        TryStmt tryStmt = parse9("try(super.a){}");
        assertInstanceOf(FieldAccessExpr.class, tryStmt.getResources().get(0));

    }

    @Test
    void outerClassAccess() {
        TryStmt tryStmt = parse9("try(X.this.a){}");
        assertInstanceOf(FieldAccessExpr.class, tryStmt.getResources().get(0));

    }

    private <T> T parse9(String code) {
        JavaParser parser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_9));
        ParseResult<Statement> result = parser.parse(ParseStart.STATEMENT, provider(code));
        assertTrue(result.isSuccessful(), result.toString());
        return (T) result.getResult().get();
    }
}
