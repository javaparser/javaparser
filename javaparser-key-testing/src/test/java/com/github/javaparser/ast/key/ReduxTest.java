package com.github.javaparser.ast.key;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.CompilationUnit;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.TestFactory;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.stream.Stream;

/**
 * @author Alexander Weigl
 * @version 1 (17.04.23)
 */
@Disabled
public class ReduxTest {
    public static final String PATHTOREDUX = "/home/weigl/work/key/key.core/src/main/resources/de/uka/ilkd/key/java/JavaRedux/java";

    @TestFactory
    Stream<DynamicTest> testRedux() throws IOException {
        return Files.walk(Paths.get(PATHTOREDUX))
                .filter(it -> it.toString().endsWith(".java"))
                .map(it -> DynamicTest.dynamicTest(it.toString(), () -> parse(it)));
    }

    JavaParser parser = new JavaParser();

    private void parse(Path it) throws IOException {
        ParseResult<CompilationUnit> res = parser.parse(it);
        if (!res.isSuccessful()) {
            res.getProblems().forEach(System.out::println);
            Assertions.fail("Problems in file: " + it);
        }
    }
}
