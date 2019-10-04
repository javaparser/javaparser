package com.github.javaparser.printer.lexicalpreservation;

import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.Optional;

import org.junit.jupiter.api.Test;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.Statement;

public class Issue2374Test {
    
    @Test
    public void test() {
        String lineComment = "Example comment";
        CompilationUnit cu = StaticJavaParser.parse(
                "public class Bar {\n" + 
                "    public void foo() {\n" + 
                "        System.out.print(\"Hello\");\n" + 
                "    }\n" + 
                "}"
                );
        LexicalPreservingPrinter.setup(cu); 
        // contruct a statement with a comment
        Statement stmt = StaticJavaParser.parseStatement("System.out.println(\"World!\");");
        stmt.setLineComment(lineComment);
        // add the statement to the ast
        Optional<MethodDeclaration> md = cu.findFirst(MethodDeclaration.class);
        md.get().getBody().get().addStatement(stmt);
        // print the result from LexicalPreservingPrinter
        String result = LexicalPreservingPrinter.print(cu);
        // verify that the LexicalPreservingPrinter don't forget the comment
        assertTrue(result.contains(lineComment));
    }
}
