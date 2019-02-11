package com.github.javaparser.ast.validator;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.stmt.Statement;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.ParseStart.STATEMENT;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.JAVA_12;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.TestUtils.assertNoProblems;

class Java12ValidatorTest {
    public static final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_12));

    @Test
    void expressionsInLabelsNotAllowed() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("switch(x){case 3+4+5: ;}"));
        assertNoProblems(result);
    }

    @Test
    void switchExpressionNotAllowed() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("int a = switch(x){};"));
        assertNoProblems(result);
    }

    @Test
    void multiLabelCaseAllowed() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("switch(x){case 3,4,5: ;}"));
        assertNoProblems(result);
    }

    @Test
    void valueBreakAllowed() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("switch(x){case 3: break 6;}"));
        assertNoProblems(result);
    }
}
