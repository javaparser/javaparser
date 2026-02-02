package com.github.javaparser.ast.key.sv;

import static org.junit.jupiter.api.Assertions.fail;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.Problem;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvFileSource;

class SchemaJavaBulkTest {
    @ParameterizedTest
    @CsvFileSource(resources = "/com/github/javaparser/schemajava.txt", delimiter = 'ä')
    void testSchemaJava(String input) {
        Assumptions.assumeFalse(input.trim().startsWith("#"));
        // System.err.println(input);
        ParserConfiguration config = new ParserConfiguration();
        config.setPreprocessUnicodeEscapes(true);
        JavaParser parser = new JavaParser(config);
        ParseResult<KeyContextStatementBlock> result = parser.parseSchemaBlock(input);

        if (!result.isSuccessful()) {
            for (Problem problem : result.getProblems()) {
                System.err.println(problem.getVerboseMessage());
            }
            fail("Parsing failed of: " + input);
        } else {
            // result.getResult().ifPresent(System.out::println);
        }
    }
}
