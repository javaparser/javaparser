package com.github.javaparser.ast.validator;

import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.stmt.Statement;
import org.junit.Test;

import static com.github.javaparser.ParseStart.STATEMENT;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.ast.validator.ValidatorTest.javaParser1_3;
import static com.github.javaparser.utils.TestUtils.assertProblems;

public class Java1_3ValidatorTest {
    @Test
    public void noAssert() {
        ParseResult<Statement> result = javaParser1_3.parse(STATEMENT, provider("assert a;"));
        assertProblems(result,
                "(line 1,col 1) 'assert' keyword is not supported"
        );
    }
}
