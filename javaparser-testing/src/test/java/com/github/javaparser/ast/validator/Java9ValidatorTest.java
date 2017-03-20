package com.github.javaparser.ast.validator;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.stmt.Statement;
import org.junit.Test;

import static com.github.javaparser.ParseStart.STATEMENT;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.TestUtils.assertProblems;

public class Java9ValidatorTest {
    public static final JavaParser javaParser = new JavaParser(new ParserConfiguration().setValidator(new Java9Validator()));

    @Test
    public void tryUnderscoreIdentifiers() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("a.b._.c.d = act(_, _ -> _);"));
        assertProblems(result,
                "(line 1,col 5) '_' is a reserved keyword.",
                "(line 1,col 17) '_' is a reserved keyword.",
                "(line 1,col 20) '_' is a reserved keyword.",
                "(line 1,col 25) '_' is a reserved keyword."
        );
    }
}
