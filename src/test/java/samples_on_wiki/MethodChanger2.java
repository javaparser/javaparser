package samples_on_wiki;

import japa.parser.ASTHelper;
import japa.parser.JavaParser;
import japa.parser.ast.CompilationUnit;
import japa.parser.ast.body.BodyDeclaration;
import japa.parser.ast.body.MethodDeclaration;
import japa.parser.ast.body.Parameter;
import japa.parser.ast.body.TypeDeclaration;

import java.io.FileInputStream;
import java.util.List;

public class MethodChanger2 {

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

        // change the methods names and parameters
        changeMethods(cu);

        // prints the changed compilation unit
        System.out.println(cu.toString());
    }

    private static void changeMethods(CompilationUnit cu) {
        List<TypeDeclaration> types = cu.getTypes();
        for (TypeDeclaration type : types) {
            List<BodyDeclaration> members = type.getMembers();
            for (BodyDeclaration member : members) {
                if (member instanceof MethodDeclaration) {
                    MethodDeclaration method = (MethodDeclaration) member;
                    changeMethod(method);
                }
            }
        }
    }

    private static void changeMethod(MethodDeclaration n) {
        // change the name of the method to upper case
        n.setName(n.getName().toUpperCase());

        // create the new parameter
        Parameter newArg = ASTHelper.createParameter(ASTHelper.INT_TYPE, "value");

        // add the parameter to the method
        ASTHelper.addParameter(n, newArg);
    }
}