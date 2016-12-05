package com.github.javaparser.junit.ast;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.Problem;
import com.github.javaparser.ast.CompilationUnit;
import org.junit.Test;

import static com.github.javaparser.ParseStart.COMPILATION_UNIT;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.Utils.EOL;
import static org.assertj.core.api.Assertions.assertThat;

public class ParseResultTest {
    private final JavaParser javaParser = new JavaParser(new ParserConfiguration());

    @Test
    public void whenParsingSucceedsThenWeGetResultsAndNoProblems() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("class X{}"));

        assertThat(result.getResult().isPresent()).isTrue();
        assertThat(result.getProblems()).isEmpty();
        assertThat(result.getTokens().isPresent()).isTrue();

        assertThat(result.toString()).isEqualTo("Parsing successful");
    }

    @Test
    public void whenParsingFailsThenWeGetProblemsAndNoResults() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("class {"));

        assertThat(result.getResult().isPresent()).isFalse();
        assertThat(result.getProblems().size()).isEqualTo(1);

        Problem problem = result.getProblem(0);
        assertThat(problem.getMessage()).startsWith("Encountered unexpected token: \"{\" \"{\"");
        assertThat(result.getTokens().isPresent()).isFalse();

        assertThat(result.toString()).startsWith("Parsing failed:" + EOL + "Encountered unexpected token:");
    }
}
