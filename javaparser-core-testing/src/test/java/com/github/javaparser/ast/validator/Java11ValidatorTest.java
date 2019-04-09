package com.github.javaparser.ast.validator;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.stmt.Statement;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.ParseStart.STATEMENT;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.JAVA_11;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.TestUtils.assertNoProblems;
import static com.github.javaparser.utils.TestUtils.assertProblems;

class Java11ValidatorTest {
    public static final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_11));

    @Test
    void varAllowedInLocalVariableDeclaration() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("x((var x, var y) -> x+y);"));
        assertNoProblems(result);
    }

    @Test
    void switchExpressionNotAllowed() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("int a = switch(x){};"));
        assertProblems(result, "(line 1,col 9) Switch expressions are not supported.");
    }

    @Test
    void multiLabelCaseNotAllowed() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("switch(x){case 3,4,5: ;}"));
        assertProblems(result, "(line 1,col 11) Only one label allowed in a switch-case.");
    }

    @Test
    void noValueBreak() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("switch(x){case 3: break 6;}"));
        assertProblems(result, "(line 1,col 19) Only labels allowed in break statements.");
    }
}
