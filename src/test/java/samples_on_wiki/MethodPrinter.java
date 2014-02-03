package samples_on_wiki;

import japa.parser.JavaParser;
import japa.parser.ast.CompilationUnit;
import japa.parser.ast.body.MethodDeclaration;
import japa.parser.ast.visitor.VoidVisitorAdapter;

import java.io.FileInputStream;

public class MethodPrinter {

    public static void main(String[] args) throws Exception {
        // creates an input stream for the file to be parsed
        FileInputStream in = new FileInputStream("src/test/java/japa/parser/ast/test/Helper.java");

        CompilationUnit cu;
        try {
            // parse the file
            cu = JavaParser.parse(in);
        } finally {
            in.close();
        }

        // visit and print the methods names
        new MethodVisitor().visit(cu, null);
    }

    /**
     * Simple visitor implementation for visiting MethodDeclaration nodes. 
     */
    private static class MethodVisitor extends VoidVisitorAdapter<Void> {

        @Override
        public void visit(MethodDeclaration n, Void arg) {
            // here you can access the attributes of the method.
            // this method will be called for all methods in this 
            // CompilationUnit, including inner class methods
            System.out.println(n.getName());
        }
    }
}