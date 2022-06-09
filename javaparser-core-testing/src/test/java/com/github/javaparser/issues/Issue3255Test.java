package com.github.javaparser.issues;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.utils.LineSeparator;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.utils.TestParser.parseStatement;
import static org.junit.jupiter.api.Assertions.assertEquals;

public class Issue3255Test {

    private static final String EOL = LineSeparator.SYSTEM.asRawString();

    @Test
    public void test() {
        JavaParser javaParser = new JavaParser();
        ParseResult<CompilationUnit> parseResult = javaParser.parse("class Test {" + EOL +
                "    private void bad() {" + EOL +
                "        String record = \"\";" + EOL +
                "        record.getBytes();" + EOL +
                "    }" + EOL +
                "}");

        assertEquals(0, parseResult.getProblems().size());

        CompilationUnit compilationUnit = parseResult.getResult().get();
        System.out.println(compilationUnit);
    }

    @Test
    public void test2() {
        JavaParser javaParser = new JavaParser();
        ParseResult<CompilationUnit> parseResult = javaParser.parse("class Test {" + EOL +
                "    private void bad() {" + EOL +
                "        String record2 = \"\";" + EOL +
                "        record2.getBytes();" + EOL +
                "    }" + EOL +
                "}");

        assertEquals(0, parseResult.getProblems().size());

        CompilationUnit compilationUnit = parseResult.getResult().get();
        System.out.println(compilationUnit);
    }

    @Test
    void recordIsAValidVariableNameWhenParsingAStatement() {
        parseStatement("Object record;");
    }

    @Test
    public void recordIsAValidVariableNameWhenUsedInAClass() {
        JavaParser javaParser = new JavaParser();
        ParseResult<CompilationUnit> parseResult = javaParser.parse("class Test {" + EOL +
                "    private void goodInJava16() {" + EOL +
                "        Object record;" + EOL +
                "    }" + EOL +
                "}");

        assertEquals(0, parseResult.getProblems().size());

        CompilationUnit compilationUnit = parseResult.getResult().get();
        System.out.println(compilationUnit);
    }

}
