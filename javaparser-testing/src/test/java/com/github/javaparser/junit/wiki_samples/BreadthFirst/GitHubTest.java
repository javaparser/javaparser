package com.github.javaparser.junit.wiki_samples.BreadthFirst;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.TreeVisitor;

import java.io.FileInputStream;
import java.io.InputStream;

public class GitHubTest {

	public static void main(String... args) throws Exception {
		FileInputStream file = new FileInputStream("forGitHubTest.java");
		CompilationUnit cu = getCompilationUnit(file);
		String result = cu.toString();
		new MyVisitor().visitBreadthFirst(cu);	
	}

	public static CompilationUnit getCompilationUnit(InputStream in) {
		try {
			CompilationUnit cu;
			try {
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

public class MyVisitor extends TreeVisitor {
	public void process(Node node) {
		System.out.println(node.toString());
	}
}
