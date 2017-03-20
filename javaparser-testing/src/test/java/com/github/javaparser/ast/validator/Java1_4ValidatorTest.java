package com.github.javaparser.ast.validator;

import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.stmt.Statement;
import org.junit.Test;

import static com.github.javaparser.ParseStart.STATEMENT;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.ast.validator.ValidatorTest.javaParser1_4;
import static com.github.javaparser.utils.TestUtils.assertNoProblems;

public class Java1_4ValidatorTest {
    @Test
    public void noAssert() {
        ParseResult<Statement> result = javaParser1_4.parse(STATEMENT, provider("assert a;"));
        assertNoProblems(result);
    }
}
