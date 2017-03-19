package com.github.javaparser.ast.validator.chunks;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.validator.Java1_1Validator;
import com.github.javaparser.ast.validator.Java8Validator;
import com.github.javaparser.ast.validator.Java9Validator;
import org.junit.Test;

import static com.github.javaparser.ParseStart.COMPILATION_UNIT;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.ast.validator.ValidatorTest.javaParser;
import static com.github.javaparser.utils.TestUtils.assertProblems;

public class ModifierValidatorTest {
}
