/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.printer;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.CastExpr;
import com.github.javaparser.ast.expr.ClassExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.type.Type;
import org.junit.Test;

import static com.github.javaparser.utils.TestUtils.assertEqualsNoEol;
import static com.github.javaparser.utils.Utils.EOL;
import static org.junit.Assert.assertEquals;

public class PrettyPrintVisitorTest {

    @Test
    public void getMaximumCommonTypeWithoutAnnotations() {
        VariableDeclarationExpr vde1 = JavaParser.parseVariableDeclarationExpr("int a[], b[]");
        assertEquals("int[]", vde1.getMaximumCommonType().get().toString());

        VariableDeclarationExpr vde2 = JavaParser.parseVariableDeclarationExpr("int[][] a[], b[]");
        assertEquals("int[][][]", vde2.getMaximumCommonType().get().toString());

        VariableDeclarationExpr vde3 = JavaParser.parseVariableDeclarationExpr("int[][] a, b[]");
        assertEquals("int[][]", vde3.getMaximumCommonType().get().toString());
    }

    @Test
    public void getMaximumCommonTypeWithAnnotations() {
        VariableDeclarationExpr vde1 = JavaParser.parseVariableDeclarationExpr("int a @Foo [], b[]");
        assertEquals("int", vde1.getMaximumCommonType().get().toString());

        VariableDeclarationExpr vde2 = JavaParser.parseVariableDeclarationExpr("int[]@Foo [] a[], b[]");
        assertEquals("int[] @Foo [][]", vde2.getMaximumCommonType().get().toString());
    }

    private String print(Node node) {
        return new PrettyPrinter().print(node);
    }

    @Test
    public void printSimpleClassExpr() {
        ClassExpr expr = JavaParser.parseExpression("Foo.class");
        assertEquals("Foo.class", print(expr));
    }

    @Test
    public void printArrayClassExpr() {
        ClassExpr expr = JavaParser.parseExpression("Foo[].class");
        assertEquals("Foo[].class", print(expr));
    }

    @Test
    public void printGenericClassExpr() {
        ClassExpr expr = JavaParser.parseExpression("Foo<String>.class");
        assertEquals("Foo<String>.class", print(expr));
    }

    @Test
    public void printSimplestClass() {
        Node node = JavaParser.parse("class A {}");
        assertEquals("class A {" + EOL +
                "}" + EOL, print(node));
    }

    @Test
    public void printAClassWithField() {
        Node node = JavaParser.parse("class A { int a; }");
        assertEquals("class A {" + EOL
                + EOL +
                "    int a;" + EOL +
                "}" + EOL, print(node));
    }

    @Test
    public void printAReceiverParameter() {
        Node node = JavaParser.parseBodyDeclaration("int x(@O X A.B.this, int y) { }");
        assertEquals("int x(@O X A.B.this, int y) {" + EOL + "}", print(node));
    }

    @Test
    public void printLambdaIntersectionTypeAssignment() {
        String code = "class A {" + EOL +
                "  void f() {" + EOL +
                "    Runnable r = (Runnable & Serializable) (() -> {});" + EOL +
                "    r = (Runnable & Serializable)() -> {};" + EOL +
                "    r = (Runnable & I)() -> {};" + EOL +
                "  }}";
        CompilationUnit cu = JavaParser.parse(code);
        MethodDeclaration methodDeclaration = (MethodDeclaration) cu.getType(0).getMember(0);

        assertEquals("Runnable r = (Runnable & Serializable) (() -> {" + EOL + "});", print(methodDeclaration.getBody().get().getStatements().get(0)));
    }

    @Test
    public void printIntersectionType() {
        String code = "(Runnable & Serializable) (() -> {})";
        Expression expression = JavaParser.parseExpression(code);
        Type type = ((CastExpr) expression).getType();

        assertEquals("Runnable & Serializable", print(type));
    }

    @Test
    public void printLambdaIntersectionTypeReturn() {
        String code = "class A {" + EOL
                + "  Object f() {" + EOL
                + "    return (Comparator<Map.Entry<K, V>> & Serializable)(c1, c2) -> c1.getKey().compareTo(c2.getKey()); " + EOL
                + "}}";
        CompilationUnit cu = JavaParser.parse(code);
        MethodDeclaration methodDeclaration = (MethodDeclaration) cu.getType(0).getMember(0);

        assertEquals("return (Comparator<Map.Entry<K, V>> & Serializable) (c1, c2) -> c1.getKey().compareTo(c2.getKey());", print(methodDeclaration.getBody().get().getStatements().get(0)));
    }

    @Test
    public void printClassWithoutJavaDocButWithComment() {
        String code = String.format("/** javadoc */ public class A { %s// stuff%s}", EOL, EOL);
        CompilationUnit cu = JavaParser.parse(code);
        PrettyPrinterConfiguration ignoreJavaDoc = new PrettyPrinterConfiguration().setPrintJavadoc(false);
        String content = cu.toString(ignoreJavaDoc);
        assertEquals(String.format("public class A {%s    // stuff%s}%s", EOL, EOL, EOL), content);
    }

    @Test
    public void printImportsDefaultOrder() {
        String code = "import x.y.z;import a.b.c;import static b.c.d;class c {}";
        CompilationUnit cu = JavaParser.parse(code);
        String content = cu.toString();
        assertEqualsNoEol("import x.y.z;\n" +
                "import a.b.c;\n" +
                "import static b.c.d;\n" +
                "\n" +
                "class c {\n" +
                "}\n", content);
    }

    @Test
    public void printImportsOrdered() {
        String code = "import x.y.z;import a.b.c;import static b.c.d;class c {}";
        CompilationUnit cu = JavaParser.parse(code);
        PrettyPrinterConfiguration orderImports = new PrettyPrinterConfiguration().setOrderImports(true);
        String content = cu.toString(orderImports);
        assertEqualsNoEol("import static b.c.d;\n" +
                "import a.b.c;\n" +
                "import x.y.z;\n" +
                "\n" +
                "class c {\n" +
                "}\n", content);
    }

    @Test
    public void multilineJavadocGetsFormatted() {
        CompilationUnit cu = new CompilationUnit();
        cu.addClass("X").addMethod("abc").setJavadocComment(" line1\n   line2 *\n * line3");

        assertEqualsNoEol("public class X {\n" +
                "\n" +
                "    /**\n" +
                "     * line1\n" +
                "     *   line2 *\n" +
                "     * line3\n" +
                "     */\n" +
                "    void abc() {\n" +
                "    }\n" +
                "}\n", cu.toString());
    }

    @Test
    public void emptyJavadocGetsFormatted() {
        CompilationUnit cu = new CompilationUnit();
        cu.addClass("X").addMethod("abc").setJavadocComment("");

        assertEqualsNoEol("public class X {\n" +
                "\n" +
                "    /**\n" +
                "     */\n" +
                "    void abc() {\n" +
                "    }\n" +
                "}\n", cu.toString());
    }

    @Test
    public void multilineJavadocWithLotsOfEmptyLinesGetsFormattedNeatly() {
        CompilationUnit cu = new CompilationUnit();
        cu.addClass("X").addMethod("abc").setJavadocComment("\n\n\n ab\n\n\n cd\n\n\n");

        assertEqualsNoEol("public class X {\n" +
                "\n" +
                "    /**\n" +
                "     * ab\n" +
                "     *\n" +
                "     * cd\n" +
                "     */\n" +
                "    void abc() {\n" +
                "    }\n" +
                "}\n", cu.toString());
    }

    @Test
    public void singlelineJavadocGetsFormatted() {
        CompilationUnit cu = new CompilationUnit();
        cu.addClass("X").addMethod("abc").setJavadocComment(" line1");

        assertEqualsNoEol("public class X {\n" +
                "\n" +
                "    /**\n" +
                "     * line1\n" +
                "     */\n" +
                "    void abc() {\n" +
                "    }\n" +
                "}\n", cu.toString());
    }

    @Test
    public void singlelineCommentGetsFormatted() {
        CompilationUnit cu = new CompilationUnit();
        cu.addClass("X").addMethod("abc").setComment(new LineComment("   line1  \n "));

        assertEqualsNoEol("public class X {\n" +
                "\n" +
                "    // line1\n" +
                "    void abc() {\n" +
                "    }\n" +
                "}\n", cu.toString());
    }

    @Test
    public void blockcommentGetsNoFormatting() {
        CompilationUnit cu = JavaParser.parse("class A {\n" +
                "    public void helloWorld(String greeting, String name) {\n" +
                "        //sdfsdfsdf\n" +
                "            //sdfds\n" +
                "        /*\n" +
                "                            dgfdgfdgfdgfdgfd\n" +
                "         */\n" +
                "    }\n" +
                "}\n");

        assertEqualsNoEol("class A {\n" +
                "\n" +
                "    public void helloWorld(String greeting, String name) {\n" +
                "    // sdfsdfsdf\n" +
                "    // sdfds\n" +
                "    /*\n" +
                "                            dgfdgfdgfdgfdgfd\n" +
                "         */\n" +
                "    }\n" +
                "}\n", cu.toString());
    }
}
