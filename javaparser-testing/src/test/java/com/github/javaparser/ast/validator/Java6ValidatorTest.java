package com.github.javaparser.ast.validator;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.stmt.Statement;
import org.junit.Test;

import static com.github.javaparser.ParseStart.STATEMENT;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.TestUtils.assertProblems;

public class Java6ValidatorTest {
    public static final JavaParser javaParser = new JavaParser(new ParserConfiguration().setValidator(new Java6Validator()));

    @Test
    public void noStringsInSwitch() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("switch(x){case \"abc\": ;}"));
        assertProblems(result, "(line 1,col 16) Strings in switch statements are not supported.");
    }

}
