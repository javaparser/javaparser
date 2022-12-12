package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.type.VoidType;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;

public class Issue2137Test extends AbstractLexicalPreservingTest {

	@Test
	void test2137() {
	    considerCode( 
	            "public class Foo {\n" +
	            "  void mymethod1() {}\n" +
	            "  void mymethod2() {}\n" +
	            "}");
	    String expected = 
	            "public class Foo {\n" +
	            "  void mymethod1() {}\n" +
	            "  void mymethod3() {\n"+
	            "  }\n" +
	            "  \n" +
	            "  void mymethod2() {}\n" +
	            "}";
	    ClassOrInterfaceDeclaration cid = cu.getClassByName("Foo").get();
	    MethodDeclaration methodDeclaration = new MethodDeclaration();
	    methodDeclaration.setName("mymethod3");
	    methodDeclaration.setType(new VoidType());
	    cid.getMembers().add(1, methodDeclaration);

	    assertEqualsStringIgnoringEol(expected, LexicalPreservingPrinter.print(cu));
	}


}
