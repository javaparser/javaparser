package com.github.javaparser.junit.wiki_samples.removenode;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.visitor.ModifierVisitorAdapter;

import java.io.FileInputStream;
import java.io.InputStream;

public class GitHubTest_2 {

    public static void main(String... args) throws Exception {
        FileInputStream file1 = new FileInputStream("forGitHubTest.java");
        CompilationUnit cu = getCompilationUnit(file1);
        String result = cu.toString();
        new MyVisitor_2().visit(cu, null);
        System.out.println(cu.toString());
    }

    public static CompilationUnit getCompilationUnit(InputStream in) {
        try {
            CompilationUnit cu;
            try {
                // parse the file
                cu = JavaParser.parse(in);
                return cu;
            } finally {
                in.close();
            }
        } catch (Exception e) {
            e.printStackTrace();
        }
        return null;
    }
}

class MyVisitor_2 extends ModifierVisitorAdapter {

    @Override
    public Node visit(ExpressionStmt stmt, Object args) {
        super.visit(stmt, args);
        if (stmt.getExpression() == null) {
            return null;
        }
        return stmt;
    }

    @Override
    public Node visit(VariableDeclarationExpr declarationExpr, Object args) {
        super.visit(declarationExpr, args);

        if (declarationExpr.getVariables().isEmpty()) {
            return null;
        }

        return declarationExpr;
    }

    @Override
    public Node visit(VariableDeclarator declarator, Object args) {
        if (declarator.getId().getName().equals("a") && declarator.getInit().toString().equals("20")) {
            return null;
        }
        return declarator;
    }

}