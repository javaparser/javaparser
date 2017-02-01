package com.github.javaparser.ast.visitor;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import org.junit.Test;

public class TreeStructureVisitorTest {
    @Test
    public void dumpSomething() {
        CompilationUnit parse = JavaParser.parse("package mypackage;\n" +
                "\n" +
                "public class MyClass {\n" +
                "\n" +
                "    public void myMethod() {\n" +
                "        if (hello() == \"abc\" && foo() == \"def\") {\n" +
                "        }\n" +
                "    }\n" +
                "}");
        parse.accept(new TreeStructureVisitor(), 0);
    }
}