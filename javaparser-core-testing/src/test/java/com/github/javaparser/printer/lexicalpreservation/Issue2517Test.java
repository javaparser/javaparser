package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;

public class Issue2517Test extends AbstractLexicalPreservingTest {

	@Test
	public void test() {

		considerCode("public class A {\n" +
	            "    public A(String a , String b) {\n" +
	            "    }\n" +
	            "    public static A m() {\n" +
	            "      return new A(\"a\",\"b\");\n" +
	            "    }\n" +
	            "}");
		
		String expected =
				"public class A {\n" +
			    "    public A(String a , String b) {\n" +
			    "    }\n" +
			    "    public static A m() {\n" +
			    "      return new A(\"b\", \"a\");\n" +
			    "    }\n" +
			    "}";

	    ObjectCreationExpr cd = cu.findFirst(ObjectCreationExpr.class).get();
	    NodeList<Expression> args = cd.getArguments();
	    Expression a1 = args.get(0);
	    Expression a2 = args.get(1);
	    NodeList<Expression> newArgs = new NodeList<>(a2, a1);
	    cd.setArguments(newArgs);

	    assertEqualsStringIgnoringEol(expected, LexicalPreservingPrinter.print(cu));
	}
}
