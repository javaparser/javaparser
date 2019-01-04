package com.github.javaparser.ast.validator;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.stmt.Statement;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.ParseStart.COMPILATION_UNIT;
import static com.github.javaparser.ParseStart.STATEMENT;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.*;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.ast.validator.Java1_1ValidatorTest.allModifiers;
import static com.github.javaparser.utils.TestUtils.assertNoProblems;
import static com.github.javaparser.utils.TestUtils.assertProblems;

class Java9ValidatorTest {
    public static final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_9));

    @Test
    void underscoreIdentifiers() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("a.b._.c.d = act(_, _ -> _);"));
        assertProblems(result,
                "(line 1,col 5) '_' is a reserved keyword.",
                "(line 1,col 17) '_' is a reserved keyword.",
                "(line 1,col 20) '_' is a reserved keyword.",
                "(line 1,col 25) '_' is a reserved keyword."
        );
    }

    @Test
    void moduleRequires() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("module x{requires " + allModifiers + " a;}"));
        assertProblems(result,
                "(line 1,col 10) Can have only one of 'public', 'protected', 'private'.",
                "(line 1,col 10) Can have only one of 'final', 'abstract'.",
                "(line 1,col 10) Can have only one of 'native', 'strictfp'.",
                "(line 1,col 10) 'transient' is not allowed here.",
                "(line 1,col 10) 'volatile' is not allowed here.",
                "(line 1,col 10) 'final' is not allowed here.",
                "(line 1,col 10) 'synchronized' is not allowed here.",
                "(line 1,col 10) 'default' is not allowed here.",
                "(line 1,col 10) 'native' is not allowed here.",
                "(line 1,col 10) 'private' is not allowed here.",
                "(line 1,col 10) 'protected' is not allowed here.",
                "(line 1,col 10) 'strictfp' is not allowed here.",
                "(line 1,col 10) 'abstract' is not allowed here.",
                "(line 1,col 10) 'public' is not allowed here."
        );
    }

    @Test
    void interfaceMethod() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("interface X{" + allModifiers + "int x(){};}"));
        assertProblems(result,
                "(line 1,col 13) Can have only one of 'public', 'protected', 'private'.",
                "(line 1,col 13) Can have only one of 'final', 'abstract'.",
                "(line 1,col 13) Can have only one of 'native', 'strictfp'.",
                "(line 1,col 13) Cannot be 'abstract' and also 'private', 'static', 'final', 'native', 'strictfp', 'synchronized'.",
                "(line 1,col 13) 'transient' is not allowed here.",
                "(line 1,col 13) 'volatile' is not allowed here.",
                "(line 1,col 13) 'transitive' is not allowed here."
        );
    }

    @Test
    void modules() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("open module x {}"));
        assertNoProblems(result);
    }

    @Test
    void tryWithResourceReference() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("try(a.b.c){}"));
        assertNoProblems(result);
    }

}
