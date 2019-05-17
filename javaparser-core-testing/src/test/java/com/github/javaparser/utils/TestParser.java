package com.github.javaparser.utils;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.stmt.Statement;

import static com.github.javaparser.ParserConfiguration.LanguageLevel.BLEEDING_EDGE;

public class TestParser {

    private static final JavaParser parser = new JavaParser(new ParserConfiguration().setLanguageLevel(BLEEDING_EDGE));

    public static CompilationUnit parseCompilationUnit(String stmt) {
        return parser.parse(stmt).getResult().get();
    }

    public static Statement parseStatement(String stmt) {
        return parser.parseStatement(stmt).getResult().get();
    }

    public static Expression parseExpression(String expr) {
        return parser.parseExpression(expr).getResult().get();
    }

    public static BodyDeclaration<?> parseBodyDeclaration(String bd) {
        return parser.parseBodyDeclaration(bd).getResult().get();
    }
}
