package com.github.javaparser.printer.lexicalpreservation;

import org.junit.jupiter.api.Test;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.NodeList;

public class Issue1634Test extends AbstractLexicalPreservingTest {

    @Test
    public void testWithLexicalPreservationEnabled() {

        String actual = "package com.wangym.test;\nclass A{ }";

        CompilationUnit cu = StaticJavaParser.parse(actual);
        LexicalPreservingPrinter.setup(cu);

        NodeList<ImportDeclaration> imports = cu.getImports();
        String str = "lombok.Data";
        imports.add(new ImportDeclaration(str, false, false));

        System.out.println(LexicalPreservingPrinter.print(cu));
    }
}
