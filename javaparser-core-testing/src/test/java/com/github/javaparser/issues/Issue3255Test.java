package com.github.javaparser.issues;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import org.junit.jupiter.api.Test;

public class Issue3255Test {

    @Test
    public void test() {
        CompilationUnit compilationUnit = StaticJavaParser.parse("class Test {\n" +
                "    private void bad() {\n" +
                "        String record = \"\";\n" +
                "        record.getBytes();\n" +
                "    }\n" +
                "}");

        System.out.println(compilationUnit);

    }

    @Test
    public void test2() {
        CompilationUnit compilationUnit = StaticJavaParser.parse("class Test {\n" +
                "    private void bad() {\n" +
                "        String record2 = \"\";\n" +
                "        record2.getBytes();\n" +
                "    }\n" +
                "}");

        System.out.println(compilationUnit);

    }
}
