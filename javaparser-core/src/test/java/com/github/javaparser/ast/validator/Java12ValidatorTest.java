package com.github.javaparser.ast.validator;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import org.junit.Test;

import static com.github.javaparser.ParserConfiguration.LanguageLevel.JAVA_12;

public class Java12ValidatorTest {
    public static final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_12));

    @Test
    public void switchExpressionAllowed() {
    }

    @Test
    public void newCaseAllowed() {
    }

    @Test
    public void multilineStringAllowed() {
    }
}
