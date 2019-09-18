package com.github.javaparser.utils;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.stmt.Statement;

import java.util.HashMap;
import java.util.Map;

import static com.github.javaparser.ParserConfiguration.*;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.BLEEDING_EDGE;
import static org.junit.jupiter.api.Assertions.fail;

public class TestParser {

    private static final Map<LanguageLevel, JavaParser> parserCache = new HashMap<>();

    private static JavaParser parser(LanguageLevel languageLevel) {
        return parserCache.computeIfAbsent(languageLevel, ll -> new JavaParser(new ParserConfiguration().setLanguageLevel(ll)));
    }

    private static <T> T unpack(ParseResult<T> result) {
        if (!result.isSuccessful()) {
            fail(result.getProblems().toString());
        }
        return result.getResult().get();
    }

    public static CompilationUnit parseCompilationUnit(String stmt) {
        return unpack(parser(BLEEDING_EDGE).parse(stmt));
    }

    public static Statement parseStatement(String stmt) {
        return unpack(parser(BLEEDING_EDGE).parseStatement(stmt));
    }

    public static <T extends Expression> T parseExpression(String expr) {
        return unpack(parser(BLEEDING_EDGE).parseExpression(expr));
    }

    public static <T extends BodyDeclaration<?>> T parseBodyDeclaration(String bd) {
        return (T) unpack(parser(BLEEDING_EDGE).parseBodyDeclaration(bd));
    }

    public static VariableDeclarationExpr parseVariableDeclarationExpr(String bd) {
        return unpack(parser(BLEEDING_EDGE).parseVariableDeclarationExpr(bd));
    }

    public static CompilationUnit parseCompilationUnit(LanguageLevel languageLevel, String stmt) {
        return unpack(parser(languageLevel).parse(stmt));
    }

    public static Statement parseStatement(LanguageLevel languageLevel, String stmt) {
        return unpack(parser(languageLevel).parseStatement(stmt));
    }

    public static <T extends Expression> T parseExpression(LanguageLevel languageLevel, String expr) {
        return unpack(parser(languageLevel).parseExpression(expr));
    }

    public static <T extends BodyDeclaration<?>> T parseBodyDeclaration(LanguageLevel languageLevel, String bd) {
        return (T) unpack(parser(languageLevel).parseBodyDeclaration(bd));
    }

    public static VariableDeclarationExpr parseVariableDeclarationExpr(LanguageLevel languageLevel, String bd) {
        return unpack(parser(languageLevel).parseVariableDeclarationExpr(bd));
    }
}
