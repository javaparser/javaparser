package com.github.javaparser.junit.wiki_samples.removenode;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.visitor.ModifierVisitorAdapter;

import java.io.FileInputStream;
import java.io.InputStream;

public class GitHubTest {

    public static void main(String... args) throws Exception {

        FileInputStream file1 = new FileInputStream("forGitHubTest.java");
        CompilationUnit cu = getCompilationUnit(file1);
        String result = cu.toString();
        new MyVisitor().visit(cu, null);
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

class MyVisitor extends ModifierVisitorAdapter {
    @Override
    public Node visit(VariableDeclarator declarator, Object args) {
        if (declarator.getIdentifier().getName().equals("a") && declarator.getInitializer().toString().equals("20")) {
            return null;
        }
        return declarator;
    }
}