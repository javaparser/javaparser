package com.github.javaparser.ast.validator;

import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.CompilationUnit;
import org.junit.Test;

import static com.github.javaparser.ParseStart.COMPILATION_UNIT;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.ast.validator.Java1_1ValidatorTest.allModifiers;
import static com.github.javaparser.ast.validator.ValidatorTest.javaParser1_0;
import static com.github.javaparser.ast.validator.ValidatorTest.javaParser8;
import static com.github.javaparser.utils.TestUtils.assertProblems;

public class Java8ValidatorTest {
    @Test
    public void localInterface() {
        ParseResult<CompilationUnit> result = javaParser8.parse(COMPILATION_UNIT, provider("class X {void a(){interface I{}};}"));
        assertProblems(result, "(line 1,col 19) There is no such thing as a local interface.");
    }

    @Test
    public void lambdaParameter() {
        ParseResult<CompilationUnit> result = javaParser8.parse(COMPILATION_UNIT, provider("class X{int x(){ a((" + allModifiers + " Integer x) -> 10);}}"));
        assertProblems(result,
                "(line 1,col 21) Can have only one of 'public', 'protected', 'private'.",
                "(line 1,col 21) Can have only one of 'final', 'abstract'.",
                "(line 1,col 21) Can have only one of 'native', 'strictfp'.",
                "(line 1,col 21) 'transient' is not allowed here.",
                "(line 1,col 21) 'volatile' is not allowed here.",
                "(line 1,col 21) 'synchronized' is not allowed here.",
                "(line 1,col 21) 'strictfp' is not allowed here.",
                "(line 1,col 21) 'default' is not allowed here.",
                "(line 1,col 21) 'native' is not allowed here.",
                "(line 1,col 21) 'strictfp' is not allowed here.",
                "(line 1,col 21) 'abstract' is not allowed here.",
                "(line 1,col 21) 'static' is not allowed here.",
                "(line 1,col 21) 'transitive' is not allowed here.",
                "(line 1,col 21) 'private' is not allowed here.",
                "(line 1,col 21) 'public' is not allowed here.",
                "(line 1,col 21) 'protected' is not allowed here."
        );
    }

    @Test
    public void defaultMethodWithoutBody() {
        ParseResult<CompilationUnit> result = javaParser8.parse(COMPILATION_UNIT, provider("interface X {default void a();}"));
        assertProblems(result, "(line 1,col 14) 'default' methods must have a body.");
    }

}
