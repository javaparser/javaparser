package com.github.javaparser;

import com.github.javaparser.ast.CompilationUnit;
import org.junit.jupiter.api.Test;

import java.io.StringReader;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class Issue3064Test {

    @Test
    public void test0() {
        String str = "import java.util.function.Supplier;\n" +
                "\n" +
                "public class MyClass {\n" +
                "\n" +
                "    public MyClass() {\n" +
                "        Supplier<String> aStringSupplier = false ? () -> \"\" : true ? () -> \"\" : () -> \"path\";\n" +
                "    }\n" +
                "}\n";

        JavaParser parser = new JavaParser();
        ParseResult<CompilationUnit> unitOpt = parser.parse(new StringReader(str));
        unitOpt.getProblems().stream().forEach(p -> System.err.println(p.toString()));
        CompilationUnit unit = unitOpt.getResult().orElseThrow(() -> new IllegalStateException("Could not parse file"));
        System.out.println(unit.toString());

        assertEquals(str, unit.toString());
    }

    @Test
    public void test1() {
        String str = "public class MyClass {\n" +
                "    {\n" +
                "        Supplier<String> aStringSupplier = false ? () -> \"F\" : true ? () -> \"T\" : () -> \"path\";\n" +
                "    }\n" +
                "}";
        CompilationUnit unit = StaticJavaParser.parse(str);
        assertEquals(str.replace("\n", ""), unit.toString().replace("\n", ""));
    }

}
