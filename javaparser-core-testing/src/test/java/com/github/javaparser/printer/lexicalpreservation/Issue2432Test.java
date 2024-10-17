package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.IfStmt;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;

public class Issue2432Test extends AbstractLexicalPreservingTest {

    @Test
    void testIfStatementIndentation() {
        String initialCode =
                "public class Example1 {\n" +
                        "  public void foo() {\n" +
                        "    System.out.println(\"Hello World!\");\n" +
                        "  }\n" +
                        "}";

        String expectedCode =
                "public class Example1 {\n" +
                        "  public void foo() {\n" +
                        "    System.out.println(\"Hello World!\");\n" +
                        "    if (13 > 12) {\n" +
                        "        System.out.println(\"!!\");\n" +
                        "    }\n" +
                        "  }\n" +
                        "}";

        JavaParser javaParser = new JavaParser();
        ParseResult<CompilationUnit> parseResult = javaParser.parse(initialCode);
        CompilationUnit compilationUnit = parseResult.getResult().get();
        LexicalPreservingPrinter.setup(compilationUnit);

        BlockStmt blockStatement = compilationUnit.findFirst(BlockStmt.class).get();

        IfStmt ifStmt = new IfStmt();
        ifStmt.setCondition(StaticJavaParser.parseExpression("13 > 12"));
        ifStmt.setThenStmt(
                new BlockStmt().addStatement(StaticJavaParser.parseStatement("System.out.println(\"!!\");")));


        blockStatement.addStatement(ifStmt);

        String actualCode = LexicalPreservingPrinter.print(compilationUnit);

        assertEqualsStringIgnoringEol(expectedCode,actualCode);
    }

}