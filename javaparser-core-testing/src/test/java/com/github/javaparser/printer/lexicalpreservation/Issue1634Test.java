package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.NodeList;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class Issue1634Test extends AbstractLexicalPreservingTest {

    @Test
    public void testWithLexicalPreservationEnabled() {

        considerCode("package com.wangym.test;\nclass A{ }");
        
        String expected =
                "package com.wangym.test;\n"
                + "import lombok.Data;\n"
                + "\n"
                + "class A{ }";

        NodeList<ImportDeclaration> imports = cu.getImports();
        String str = "lombok.Data";
        imports.add(new ImportDeclaration(str, false, false));

        assertEquals(expected, LexicalPreservingPrinter.print(cu));
    }
}
