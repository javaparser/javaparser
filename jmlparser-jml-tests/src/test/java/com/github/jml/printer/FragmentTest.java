package com.github.jml.printer;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.Providers;
import com.github.javaparser.ast.jml.ArbitraryNodeContainer;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.TestFactory;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.Arrays;
import java.util.stream.Stream;

/**
 * @author Alexander Weigl
 * @version 1 (12/9/21)
 */
public class FragmentTest {
    @TestFactory
    public Stream<DynamicTest> testStatementLevel() {
        return files()
                .filter(it -> it.getName().startsWith("stmt"))
                .map(it -> DynamicTest.dynamicTest(it.getName(), () -> testStatementLevel(it)));
    }

    private void testStatementLevel(File f) throws FileNotFoundException {
        JavaParser jp = new JavaParser();
        ParseResult<ArbitraryNodeContainer> r = jp.parseJmlMethodLevel(Providers.provider(f));
        Assumptions.assumeFalse(r.getProblems().stream().anyMatch(it -> ignorableMessages(it.getMessage())));

        r.getProblems().forEach(
                it -> System.out.println(it.getMessage())
        );
        Assertions.assertTrue(r.isSuccessful());
    }

    @TestFactory
    public Stream<DynamicTest> testClassLevel() {
        return files()
                .filter(it -> it.getName().startsWith("decl"))
                //.filter(it -> it.getName().endsWith("510942598.txt"))
                .map(it -> DynamicTest.dynamicTest(it.getName(), () -> testClassLevel(it)));
    }

    private void testClassLevel(File f) throws FileNotFoundException {
        JavaParser jp = new JavaParser();
        ParseResult<ArbitraryNodeContainer> r = jp.parseJmlClassLevel(Providers.provider(f));

        Assumptions.assumeFalse(r.getProblems().stream().anyMatch(it -> ignorableMessages(it.getMessage())));

        r.getProblems().forEach(
                it -> System.out.println(it.getMessage())
        );
        Assertions.assertTrue(r.isSuccessful());
    }

    private boolean ignorableMessages(String message) {
        return message.contains("model_program")
                || message.contains("recommends")
                || message.contains("class")
                || message.contains("skipesc")
                || message.contains("split")
                || message.contains("function")
                || message.contains("loop_writes")
                || message.contains("loop_modifies")
                || message.contains("reachable")
                || message.contains("debug")
                || message.contains("havoc")
                || message.contains("show")
                || message.contains("begin")
                || message.contains("end")
                || message.contains("loop_decreases")
                || message.contains("check");
    }


    private Stream<File> files() {
        File[] files = new File("src/test/resources/fragments").listFiles();
        assert files != null;
        Arrays.sort(files);
        return Arrays.stream(files);
    }
}
