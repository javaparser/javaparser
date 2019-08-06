package com.github.javaparser.utils;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.stmt.Statement;

import static com.github.javaparser.ParserConfiguration.LanguageLevel.BLEEDING_EDGE;
import static org.junit.jupiter.api.Assertions.fail;

public class TestParser {

    private static final JavaParser parser = new JavaParser(new ParserConfiguration().setLanguageLevel(BLEEDING_EDGE));

    private static <T> T unpack(ParseResult<T> result) {
        if (!result.isSuccessful()) {
            fail(result.getProblems().toString());
        }
        return result.getResult().get();
    }

    public static CompilationUnit parseCompilationUnit(String stmt) {
        return unpack(parser.parse(stmt));
    }

    public static Statement parseStatement(String stmt) {
        return unpack(parser.parseStatement(stmt));
    }

    public static <T extends Expression> T parseExpression(String expr) {
        return unpack(parser.parseExpression(expr));
    }

    public static <T extends BodyDeclaration<?>> T parseBodyDeclaration(String bd) {
        return (T) unpack(parser.parseBodyDeclaration(bd));
    }

    public static VariableDeclarationExpr parseVariableDeclarationExpr(String bd) {
        return unpack(parser.parseVariableDeclarationExpr(bd));
    }
}
