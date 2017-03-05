package com.github.javaparser.ast.validator;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.CompilationUnit;
import org.junit.Test;

import static com.github.javaparser.ParseStart.COMPILATION_UNIT;
import static com.github.javaparser.Providers.provider;
import static org.junit.Assert.assertEquals;

public class ValidatorTest {
    @Test
    public void noProblemsHere() {
        ParseResult<CompilationUnit> result = new JavaParser().parse(COMPILATION_UNIT, provider("class X{}"), new NoProblemsValidator());
        assertEquals(true, result.isSuccessful());
    }

}
