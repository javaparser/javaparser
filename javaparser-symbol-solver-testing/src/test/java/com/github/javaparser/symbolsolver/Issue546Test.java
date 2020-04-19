package com.github.javaparser.symbolsolver;

import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.printer.PrettyPrinter;
import com.github.javaparser.printer.PrettyPrinterConfiguration;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parseStatement;
import static com.github.javaparser.utils.Utils.EOL;
import static com.github.javaparser.utils.Utils.normalizeEolInTextBlock;
import static org.junit.jupiter.api.Assertions.assertEquals;

public class Issue546Test {
    @Test
    void switchWithTabs() {
        Statement cu = parseStatement("switch(x){ case 1: return y; case 2: return z;}");

        String printed = new PrettyPrinter(new PrettyPrinterConfiguration())
                .print(cu);
        assertEqualsNoEol("switch(x) {\n" +
                "    case 1:\n" +
                "        return y;\n" +
                "    case 2:\n" +
                "        return z;\n" +
                "}", printed);
    }
    @Test
    void switchWithoutTabs() {
        Statement cu = parseStatement("switch(x){ case 1: return y; case 2: return z;}");

        String printed = new PrettyPrinter(new PrettyPrinterConfiguration().setIndentCaseInSwitch(false))
                .print(cu);
        assertEqualsNoEol("switch(x) {\n" +
                "case 1:\n" +
                "    return y;\n" +
                "case 2:\n" +
                "    return z;\n" +
                "}", printed);
    }

    public static void assertEqualsNoEol(String expected, String actual) {
        assertEquals(normalizeEolInTextBlock(expected, EOL), actual);
    }
}
