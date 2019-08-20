package com.github.javaparser.ast.stmt;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.BinaryExpr;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.ParserConfiguration.LanguageLevel.JAVA_12;
import static com.github.javaparser.utils.TestParser.parseCompilationUnit;
import static com.github.javaparser.utils.TestParser.parseStatement;
import static com.github.javaparser.utils.TestUtils.assertEqualsNoEol;
import static org.junit.jupiter.api.Assertions.assertEquals;

class YieldStmtTest {
    @Test
    void yield() {
        YieldStmt statement = parseStatement("yield 12*12;").asYieldStmt();
        assertEquals(BinaryExpr.class, statement.getExpression().getClass());
    }

    @Test
    void threadYieldShouldNotBreak() {
        parseStatement("Thread.yield();").asExpressionStmt().getExpression().asMethodCallExpr();
    }

    @Test
    void keywordShouldNotInterfereWithIdentifiers() {
        CompilationUnit compilationUnit = parseCompilationUnit(JAVA_12, "class yield { yield yield(yield yield){yield();} }");
        assertEqualsNoEol("class yield {\n" +
                "\n" +
                "    yield yield(yield yield) {\n" +
                "        yield();\n" +
                "    }\n" +
                "}\n", compilationUnit.toString());
    }
}