package com.github.javaparser.junit.wiki_samples;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;

import java.io.File;
import java.io.FileInputStream;

import static com.github.javaparser.ast.type.PrimitiveType.INT_TYPE;

public class MethodChanger_1 {

    public static void main(String[] args) throws Exception {
        // parse a file
        CompilationUnit cu = JavaParser.parse(new File("test.java"));

        // visit and change the methods names and parameters
        new MethodChangerVisitor().visit(cu, null);

        // prints the changed compilation unit
        System.out.println(cu);
    }

    /**
     * Simple visitor implementation for visiting MethodDeclaration nodes.
     */
    private static class MethodChangerVisitor extends VoidVisitorAdapter<Object> {
        @Override
        public void visit(MethodDeclaration n, Object arg) {
            // change the name of the method to upper case
            n.setName(n.getNameAsString().toUpperCase());

            // add a new parameter to the method
            n.addParameter("int", "value");
        }
    }
}