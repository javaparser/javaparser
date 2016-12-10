package com.github.javaparser.junit.wiki_samples.removenode;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.visitor.ModifierVisitor;

import java.io.FileInputStream;

public class ModifierVisitorTest {

    public static void main(String... args) throws Exception {
        // parse the file
        CompilationUnit cu = JavaParser.parse(new FileInputStream("forGitHubTest.java"));

        // The visitor should remove all a=20 variable declarations.
        new MyVisitor().visit(cu, null);

        System.out.println(cu.toString());
    }
}

class MyVisitor extends ModifierVisitor<Void> {
    @Override
    public Node visit(VariableDeclarator declarator, Void args) {
        if (declarator.getNameAsString().equals("a")
                // the initializer is optional, first check if there is one
                && declarator.getInitializer().isPresent()) {
            Expression expression = declarator.getInitializer().get();
            // We're looking for a literal integer.
            if (expression instanceof IntegerLiteralExpr) {
                // We found one. Is it literal integer 20?
                if (((IntegerLiteralExpr) expression).getValue().equals("20")) {
                    // Returning null means "remove this VariableDeclarator"
                    return null;
                }
            }
        }
        return declarator;
    }
}