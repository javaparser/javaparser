package com.github.javaparser.ast.validator;

import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.CompilationUnit;
import org.junit.Test;

import static com.github.javaparser.ParseStart.COMPILATION_UNIT;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.ast.validator.ValidatorTest.javaParser1_0;
import static com.github.javaparser.ast.validator.ValidatorTest.javaParser7;
import static com.github.javaparser.utils.TestUtils.assertNoProblems;
import static com.github.javaparser.utils.TestUtils.assertProblems;

public class Java7ValidatorTest {
    @Test
    public void generics() {
        ParseResult<CompilationUnit> result = javaParser7.parse(COMPILATION_UNIT, provider("class X<A>{List<String> b = new ArrayList<>();}"));
        assertNoProblems(result);
    }
    @Test
    public void defaultMethodWithoutBody() {
        ParseResult<CompilationUnit> result = javaParser7.parse(COMPILATION_UNIT, provider("interface X {default void a(){};}"));
        assertProblems(result, "(line 1,col 14) 'default' is not allowed here.");
    }

}
