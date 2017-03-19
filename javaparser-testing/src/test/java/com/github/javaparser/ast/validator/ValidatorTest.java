package com.github.javaparser.ast.validator;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.stmt.Statement;
import org.junit.Test;

import static com.github.javaparser.ParseStart.STATEMENT;
import static com.github.javaparser.Providers.provider;
import static org.junit.Assert.assertEquals;

public class ValidatorTest {
    public static final JavaParser javaParser = new JavaParser(new ParserConfiguration().setValidator(new Java9Validator()));
    public static final JavaParser javaParser9 = new JavaParser(new ParserConfiguration().setValidator(new Java9Validator()));
    public static final JavaParser javaParser8 = new JavaParser(new ParserConfiguration().setValidator(new Java8Validator()));
    public static final JavaParser javaParser7 = new JavaParser(new ParserConfiguration().setValidator(new Java7Validator()));
    public static final JavaParser javaParser6 = new JavaParser(new ParserConfiguration().setValidator(new Java6Validator()));
    public static final JavaParser javaParser5 = new JavaParser(new ParserConfiguration().setValidator(new Java5Validator()));
    public static final JavaParser javaParser1_4 = new JavaParser(new ParserConfiguration().setValidator(new Java1_4Validator()));
    public static final JavaParser javaParser1_3 = new JavaParser(new ParserConfiguration().setValidator(new Java1_3Validator()));
    public static final JavaParser javaParser1_2 = new JavaParser(new ParserConfiguration().setValidator(new Java1_2Validator()));
    public static final JavaParser javaParser1_1 = new JavaParser(new ParserConfiguration().setValidator(new Java1_1Validator()));
    public static final JavaParser javaParser1_0 = new JavaParser(new ParserConfiguration().setValidator(new Java1_0Validator()));

    @Test
    public void noProblemsHere() {
        ParseResult<Statement> result =
                new JavaParser(new ParserConfiguration().setValidator(new NoProblemsValidator()))
                        .parse(STATEMENT, provider("try{}"));
        assertEquals(true, result.isSuccessful());
    }

}
