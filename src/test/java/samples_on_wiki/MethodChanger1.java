package samples_on_wiki;

import japa.parser.ASTHelper;
import japa.parser.JavaParser;
import japa.parser.ast.CompilationUnit;
import japa.parser.ast.body.MethodDeclaration;
import japa.parser.ast.body.Parameter;
import japa.parser.ast.visitor.VoidVisitorAdapter;

import java.io.FileInputStream;

public class MethodChanger1 {

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

        // visit and change the methods names and parameters
        new MethodChangerVisitor().visit(cu, null);

        // prints the changed compilation unit
        System.out.println(cu.toString());
    }

    /**
     * Simple visitor implementation for visiting MethodDeclaration nodes.
     */
    private static class MethodChangerVisitor extends VoidVisitorAdapter<Void> {

        @Override
        public void visit(MethodDeclaration n, Void arg) {
            // change the name of the method to upper case
            n.setName(n.getName().toUpperCase());

            // create the new parameter
            Parameter newArg = ASTHelper.createParameter(ASTHelper.INT_TYPE, "value");

            // add the parameter to the method
            ASTHelper.addParameter(n, newArg);
        }
    }
}