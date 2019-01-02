package com.github.javaparser.ast.validator;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.ParserConfiguration.LanguageLevel.JAVA_12;

class Java12ValidatorTest {
    public static final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_12));

    @Test
    void switchExpressionAllowed() {
    }

    @Test
    void newCaseAllowed() {
    }

    @Test
    void multilineStringAllowed() {
    }
}
