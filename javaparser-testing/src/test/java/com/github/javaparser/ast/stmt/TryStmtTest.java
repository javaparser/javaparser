package com.github.javaparser.ast.stmt;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParseStart;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.validator.Java9Validator;
import org.junit.Test;

import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.TestUtils.assertInstanceOf;
import static org.junit.Assert.assertTrue;

public class TryStmtTest {
    @Test
    public void simpleTest() {
        TryStmt tryStmt = parse9("try(Reader x = new FileReader()){}");
        assertInstanceOf(VariableDeclarationExpr.class, tryStmt.getResources().get(0));
    }

    @Test
    public void multipleTest() {
        TryStmt tryStmt = parse9("try(Reader x = new FileReader(); Reader x = new FileReader()){}");
        assertInstanceOf(VariableDeclarationExpr.class, tryStmt.getResources().get(0));

    }

    @Test
    public void modifiersTest() {
        TryStmt tryStmt = parse9("try(final @A Reader x = new FileReader()){}");
        assertInstanceOf(VariableDeclarationExpr.class, tryStmt.getResources().get(0));

    }

    @Test
    public void simpleVariable() {
        TryStmt tryStmt = parse9("try(a){}");
        assertInstanceOf(NameExpr.class, tryStmt.getResources().get(0));

    }

    @Test
    public void twoSimpleVariables() {
        TryStmt tryStmt = parse9("try(a;b){}");
        assertInstanceOf(NameExpr.class, tryStmt.getResources().get(0));
        assertInstanceOf(NameExpr.class, tryStmt.getResources().get(1));

    }

    @Test
    public void complexVariable() {
        TryStmt tryStmt = parse9("try(a.b.c){}");
        assertInstanceOf(FieldAccessExpr.class, tryStmt.getResources().get(0));

    }

    @Test
    public void superAccess() {
        TryStmt tryStmt = parse9("try(super.a){}");
        assertInstanceOf(FieldAccessExpr.class, tryStmt.getResources().get(0));

    }

    @Test
    public void outerClassAccess() {
        TryStmt tryStmt = parse9("try(X.this.a){}");
        assertInstanceOf(FieldAccessExpr.class, tryStmt.getResources().get(0));

    }

    private <T> T parse9(String code) {
        JavaParser parser = new JavaParser(new ParserConfiguration().setValidator(new Java9Validator()));
        ParseResult<Statement> result = parser.parse(ParseStart.STATEMENT, provider(code));
        assertTrue(result.toString(), result.isSuccessful());
        return (T) result.getResult().get();
    }
}
