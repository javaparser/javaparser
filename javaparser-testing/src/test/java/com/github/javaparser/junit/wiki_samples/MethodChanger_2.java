package com.github.javaparser.junit.wiki_samples;

import java.io.FileInputStream;
import java.util.List;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;

import static com.github.javaparser.ast.type.PrimitiveType.*;

public class MethodChanger_2 {

    public static void main(String[] args) throws Exception {
        // creates an input stream for the file to be parsed

        CompilationUnit cu;
        try (FileInputStream in = new FileInputStream("test.java")) {
            // parse the file
            cu = JavaParser.parse(in);
        }

        // change the methods names and parameters
        changeMethods(cu);

        // prints the changed compilation unit
        System.out.println(cu.toString());
    }

    private static void changeMethods(CompilationUnit cu) {
		NodeList<TypeDeclaration<?>> types = cu.getTypes();
		for (TypeDeclaration<?> type : types) {
			List<BodyDeclaration<?>> members = type.getMembers();
			for (BodyDeclaration<?> member : members) {
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
        n.addParameter(INT_TYPE, "value");
    }
}
