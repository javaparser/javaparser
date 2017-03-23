package com.github.javaparser.ast.validator;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.stmt.Statement;
import org.junit.Test;

import static com.github.javaparser.ParseStart.COMPILATION_UNIT;
import static com.github.javaparser.ParseStart.EXPRESSION;
import static com.github.javaparser.ParseStart.STATEMENT;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.TestUtils.assertNoProblems;
import static com.github.javaparser.utils.TestUtils.assertProblems;

public class Java7ValidatorTest {
    public static final JavaParser javaParser = new JavaParser(new ParserConfiguration().setValidator(new Java7Validator()));

    @Test
    public void generics() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("class X<A>{List<String> b = new ArrayList<>();}"));
        assertNoProblems(result);
    }

    @Test
    public void defaultMethodWithoutBody() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("interface X {default void a();}"));
        assertProblems(result, "(line 1,col 14) 'default' is not allowed here.");
    }

    @Test
    public void tryWithoutAnything() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("try{}"));
        assertProblems(result, "(line 1,col 1) Try has no finally, no catch, and no resources.");
    }

    @Test
    public void stringsInSwitch() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("switch(x){case \"abc\": ;}"));
        assertNoProblems(result);
    }

    @Test
    public void nobinaryIntegerLiterals() {
        ParseResult<Expression> result = javaParser.parse(EXPRESSION, provider("0b01"));
        assertNoProblems(result);
    }

    @Test
    public void noUnderscoresInIntegerLiterals() {
        ParseResult<Expression> result = javaParser.parse(EXPRESSION, provider("1_000_000"));
        assertNoProblems(result);
    }

    @Test
    public void noMultiCatch() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("try{}catch(Abc|Def e){}"));
        assertNoProblems(result);
    }
}
