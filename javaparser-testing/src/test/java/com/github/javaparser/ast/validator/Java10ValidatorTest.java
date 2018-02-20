package com.github.javaparser.ast.validator;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.stmt.Statement;
import org.junit.Test;

import static com.github.javaparser.ParseStart.COMPILATION_UNIT;
import static com.github.javaparser.ParseStart.STATEMENT;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.*;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.ast.validator.Java1_1ValidatorTest.allModifiers;
import static com.github.javaparser.utils.TestUtils.assertNoProblems;
import static com.github.javaparser.utils.TestUtils.assertProblems;

public class Java10ValidatorTest {
    public static final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_10_PREVIEW));

    @Test
    public void varAllowedInLocalVariableDeclaration() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("var a = 5;"));
        assertNoProblems(result);
    }

    @Test
    public void varAllowedInForEach() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("for(var a : as){}"));
        assertNoProblems(result);
    }

    @Test
    public void varAllowedInOldFor() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("for(var a = 5;a<9;a++){}"));
        assertNoProblems(result);
    }

    @Test
    public void varNotAllowedInCast() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("int a = (var)20;"));
        assertNoProblems(result);
    }

    @Test
    public void varNotAllowedInTypeArguments() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("new X<var>();"));
        assertProblems(result, "(line 1,col 7) \"var\" is not allowed here.");
    }

    @Test
    public void varNotAllowedInLambdaParameters() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("x((var x) -> null);"));
        assertProblems(result, "(line 1,col 4) \"var\" is not allowed here.");
    }
}
