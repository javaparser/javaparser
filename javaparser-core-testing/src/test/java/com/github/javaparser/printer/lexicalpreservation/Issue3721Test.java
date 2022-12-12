package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.ast.body.VariableDeclarator;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;

public class Issue3721Test extends AbstractLexicalPreservingTest {

    @Test
    void issue3721() {
        considerCode(
                "public class Bug {\n"
                + "    public static void main(String[] args) {\n"
                + "        Object msg;\n"
                + "    }\n"
                + "}\n");
        
        String expected =
                "public class Bug {\n"
                + "\n"
                + "    public static void main(String[] args) {\n"
                + "        boolean msg;\n"
                + "    }\n"
                + "}\n";
                

        VariableDeclarator var = cu.findFirst(VariableDeclarator.class).get();
        var.setType("boolean");
        assertEqualsStringIgnoringEol(expected, cu.toString());
    }
}
