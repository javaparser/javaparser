package com.github.javaparser.junit.wiki_samples;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;

import java.io.FileInputStream;

import static com.github.javaparser.ast.type.PrimitiveType.*;

public class MethodChanger_1 {

    public static void main(String[] args) throws Exception {
        // creates an input stream for the file to be parsed

        CompilationUnit cu;
        try (FileInputStream in = new FileInputStream("test.java")) {
            // parse the file
            cu = JavaParser.parse(in);
        }

        // visit and change the methods names and parameters
        new MethodChangerVisitor().visit(cu, null);

        // prints the changed compilation unit
        System.out.println(cu.toString());
    }

    /**
     * Simple visitor implementation for visiting MethodDeclaration nodes.
     */
    private static class MethodChangerVisitor extends VoidVisitorAdapter<Object> {

        @Override
        public void visit(MethodDeclaration n, Object arg) {
            // change the name of the method to upper case
            n.setName(n.getNameAsString().toUpperCase());

            // create the new parameter
            n.addParameter(INT_TYPE, "value");
        }
    }
}