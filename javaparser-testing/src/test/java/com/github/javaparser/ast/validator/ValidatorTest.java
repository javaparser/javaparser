package com.github.javaparser.ast.validator;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.stmt.Statement;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.ParseStart.STATEMENT;
import static com.github.javaparser.Providers.provider;
import static org.junit.jupiter.api.Assertions.assertEquals;

public class ValidatorTest {
    public static final JavaParser javaParser = new JavaParser(new ParserConfiguration().setValidator(new Java9Validator()));

    @Test
    public void noProblemsHere() {
        ParseResult<Statement> result =
                new JavaParser(new ParserConfiguration().setValidator(new NoProblemsValidator()))
                        .parse(STATEMENT, provider("try{}"));
        assertEquals(true, result.isSuccessful());
    }

}
