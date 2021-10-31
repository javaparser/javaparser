package com.github.javaparser.ast.key.sv;

import com.github.javaparser.*;
import com.github.javaparser.ParserConfiguration.LanguageLevel;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvFileSource;

import static com.github.javaparser.ParserConfiguration.LanguageLevel.BLEEDING_EDGE;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.CURRENT;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.fail;

public class SchemaJavaBulkTest {
    @BeforeEach
    void setToLatestJava() {
        StaticJavaParser.getConfiguration().setLanguageLevel(LanguageLevel.BLEEDING_EDGE);
    }

    @AfterEach
    void resetJavaLevel() {
        StaticJavaParser.getConfiguration().setLanguageLevel(LanguageLevel.CURRENT);
    }


    @ParameterizedTest
    @CsvFileSource(resources = "/com/github/javaparser/schemajava.txt", delimiter = 'ä')
    public void testSchemaJava(String input) {
        ParserConfiguration config = new ParserConfiguration();
        config.setPreprocessUnicodeEscapes(true);
        JavaParser parser = new JavaParser(config);
        ParseResult<KeyContextStatementBlock> result = parser.parseSchemaBlock(input);

        if(!result.isSuccessful()) {
            for (Problem problem : result.getProblems()) {
                System.err.println(problem);
            }
            fail(result.toString());
        } else {
            result.getResult().ifPresent(it -> {
                System.out.println(it.toString());
            });
        }
    }
}
