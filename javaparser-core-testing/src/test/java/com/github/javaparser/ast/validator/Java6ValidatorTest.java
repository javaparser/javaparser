package com.github.javaparser.ast.validator;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.stmt.Statement;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.ParseStart.EXPRESSION;
import static com.github.javaparser.ParseStart.STATEMENT;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.*;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.TestUtils.assertProblems;

class Java6ValidatorTest {
    public static final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_6));

    @Test
    void nobinaryIntegerLiterals() {
        ParseResult<Expression> result = javaParser.parse(EXPRESSION, provider("0b01"));
        assertProblems(result, "(line 1,col 1) Binary literal values are not supported.");
    }

    @Test
    void noUnderscoresInIntegerLiterals() {
        ParseResult<Expression> result = javaParser.parse(EXPRESSION, provider("1_000_000"));
        assertProblems(result, "(line 1,col 1) Underscores in literal values are not supported.");
    }

    @Test
    void noMultiCatch() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("try{}catch(Abc|Def e){}"));
        assertProblems(result, "(line 1,col 12) Multi-catch is not supported.");
    }
}
