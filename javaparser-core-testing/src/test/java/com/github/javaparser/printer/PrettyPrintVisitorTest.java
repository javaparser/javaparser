/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
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

import static com.github.javaparser.StaticJavaParser.parse;
import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;
import static org.junit.jupiter.api.Assertions.assertEquals;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.CastExpr;
import com.github.javaparser.ast.expr.ClassExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.printer.configuration.ConfigurationOption;
import com.github.javaparser.printer.configuration.DefaultConfigurationOption;
import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration;
import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration.ConfigOption;
import com.github.javaparser.printer.configuration.PrinterConfiguration;
import com.github.javaparser.utils.LineSeparator;
import com.github.javaparser.utils.TestParser;
import java.util.Optional;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

class PrettyPrintVisitorTest extends TestParser {
    @BeforeAll
    static void initParser() {
        StaticJavaParser.getParserConfiguration().setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_25);
    }

    private Optional<ConfigurationOption> getOption(PrinterConfiguration config, ConfigOption cOption) {
        return config.get(new DefaultConfigurationOption(cOption));
    }

    @Test
    void getMaximumCommonTypeWithoutAnnotations() {
        VariableDeclarationExpr vde1 = parseVariableDeclarationExpr("int a[], b[]");
        assertEquals("int[]", vde1.getMaximumCommonType().get().toString());

        VariableDeclarationExpr vde2 = parseVariableDeclarationExpr("int[][] a[], b[]");
        assertEquals("int[][][]", vde2.getMaximumCommonType().get().toString());

        VariableDeclarationExpr vde3 = parseVariableDeclarationExpr("int[][] a, b[]");
        assertEquals("int[][]", vde3.getMaximumCommonType().get().toString());
    }

    @Test
    void getMaximumCommonTypeWithAnnotations() {
        VariableDeclarationExpr vde1 = parseVariableDeclarationExpr("int a @Foo [], b[]");
        assertEquals("int", vde1.getMaximumCommonType().get().toString());

        VariableDeclarationExpr vde2 = parseVariableDeclarationExpr("int[]@Foo [] a[], b[]");
        assertEquals("int[][] @Foo []", vde2.getMaximumCommonType().get().toString());
    }

    private String print(Node node) {
        return new DefaultPrettyPrinter().print(node);
    }

    private String print(Node node, PrinterConfiguration conf) {
        return new DefaultPrettyPrinter(conf).print(node);
    }

    @Test
    void printSimpleClassExpr() {
        ClassExpr expr = parseExpression("Foo.class");
        assertEquals("Foo.class", print(expr));
    }

    /**
     * Here is a simple test according to R0 (removing spaces)
     */
    @Test
    void printOperatorsR0() {
        PrinterConfiguration conf1 = new DefaultPrinterConfiguration()
                .removeOption(new DefaultConfigurationOption(ConfigOption.SPACE_AROUND_OPERATORS));
        Statement statement1 = parseStatement("a = 1 + 1;");
        assertEquals("a=1+1;", print(statement1, conf1));
    }

    /**
     * Here we test different operators according to requirement R1 (handling different operators)
     */
    @Test
    void printOperatorsR1() {

        Statement statement1 = parseStatement("a = 1 + 1;");
        assertEquals("a = 1 + 1;", print(statement1));

        Statement statement2 = parseStatement("a = 1 - 1;");
        assertEquals("a = 1 - 1;", print(statement2));

        Statement statement3 = parseStatement("a = 1 * 1;");
        assertEquals("a = 1 * 1;", print(statement3));

        Statement statement4 = parseStatement("a = 1 % 1;");
        assertEquals("a = 1 % 1;", print(statement4));

        Statement statement5 = parseStatement("a=1/1;");
        assertEquals("a = 1 / 1;", print(statement5));

        Statement statement6 = parseStatement("if (1 > 2 && 1 < 3 || 1 < 3){}");
        assertEquals("if (1 > 2 && 1 < 3 || 1 < 3) {" + LineSeparator.SYSTEM + "}", print(statement6));
    }

    /**
     * Here is a simple test according to R2 (that it should be optional/modifiable)
     */
    @Test
    void printOperatorsR2() {
        PrinterConfiguration conf1 = new DefaultPrinterConfiguration()
                .removeOption(new DefaultConfigurationOption(ConfigOption.SPACE_AROUND_OPERATORS));
        Statement statement1 = parseStatement("a = 1 + 1;");
        assertEquals("a=1+1;", print(statement1, conf1));

        PrinterConfiguration conf2 = new DefaultPrinterConfiguration()
                .removeOption(new DefaultConfigurationOption(ConfigOption.SPACE_AROUND_OPERATORS));
        Statement statement2 = parseStatement("a=1+1;");
        assertEquals("a=1+1;", print(statement2, conf2));

        PrinterConfiguration conf3 = new DefaultPrinterConfiguration()
                .addOption(new DefaultConfigurationOption(ConfigOption.SPACE_AROUND_OPERATORS));
        Statement statement3 = parseStatement("a = 1 + 1;");
        assertEquals("a = 1 + 1;", print(statement3, conf3));

        PrinterConfiguration conf4 = new DefaultPrinterConfiguration()
                .addOption(new DefaultConfigurationOption(ConfigOption.SPACE_AROUND_OPERATORS));
        Statement statement4 = parseStatement("a=1+1;");
        assertEquals("a = 1 + 1;", print(statement4, conf4));
    }

    @Test
    void printOperatorA() {
        PrinterConfiguration conf = new DefaultPrinterConfiguration()
                .removeOption(new DefaultConfigurationOption(ConfigOption.SPACE_AROUND_OPERATORS));
        Statement statement6 = parseStatement("if(1>2&&1<3||1<3){}");
        assertEquals("if (1>2&&1<3||1<3) {" + LineSeparator.SYSTEM + "}", print(statement6, conf));
    }

    @Test
    void printOperator2() {
        Expression expression = parseExpression("1+1");
        PrinterConfiguration spaces = new DefaultPrinterConfiguration()
                .removeOption(new DefaultConfigurationOption(ConfigOption.SPACE_AROUND_OPERATORS));
        assertEquals("1+1", print(expression, spaces));
    }

    @Test
    void printArrayClassExpr() {
        ClassExpr expr = parseExpression("Foo[].class");
        assertEquals("Foo[].class", print(expr));
    }

    @Test
    void printGenericClassExpr() {
        ClassExpr expr = parseExpression("Foo<String>.class");
        assertEquals("Foo<String>.class", print(expr));
    }

    @Test
    void printSimplestClass() {
        Node node = parse("class A {}");
        assertEquals("class A {" + LineSeparator.SYSTEM + "}" + LineSeparator.SYSTEM, print(node));
    }

    @Test
    void printAClassWithField() {
        Node node = parse("class A { int a; }");
        assertEquals(
                "class A {" + LineSeparator.SYSTEM
                        + LineSeparator.SYSTEM + "    int a;"
                        + LineSeparator.SYSTEM + "}"
                        + LineSeparator.SYSTEM,
                print(node));
    }

    @Test
    void printAReceiverParameter() {
        Node node = parseBodyDeclaration("int x(@O X A.B.this, int y) { }");
        assertEquals("int x(@O X A.B.this, int y) {" + LineSeparator.SYSTEM + "}", print(node));
    }

    @Test
    void printLambdaIntersectionTypeAssignment() {
        String code = "class A {" + LineSeparator.SYSTEM + "  void f() {"
                + LineSeparator.SYSTEM + "    Runnable r = (Runnable & Serializable) (() -> {});"
                + LineSeparator.SYSTEM + "    r = (Runnable & Serializable)() -> {};"
                + LineSeparator.SYSTEM + "    r = (Runnable & I)() -> {};"
                + LineSeparator.SYSTEM + "  }}";
        CompilationUnit cu = parse(code);
        MethodDeclaration methodDeclaration = (MethodDeclaration) cu.getType(0).getMember(0);

        assertEquals(
                "Runnable r = (Runnable & Serializable) (() -> {" + LineSeparator.SYSTEM + "});",
                print(methodDeclaration.getBody().get().getStatements().get(0)));
    }

    @Test
    void printIntersectionType() {
        String code = "(Runnable & Serializable) (() -> {})";
        Expression expression = parseExpression(code);
        Type type = ((CastExpr) expression).getType();

        assertEquals("Runnable & Serializable", print(type));
    }

    @Test
    void printLambdaIntersectionTypeReturn() {
        String code = "class A {" + LineSeparator.SYSTEM
                + "  Object f() {" + LineSeparator.SYSTEM
                + "    return (Comparator<Map.Entry<K, V>> & Serializable)(c1, c2) -> c1.getKey().compareTo(c2.getKey()); "
                + LineSeparator.SYSTEM
                + "}}";
        CompilationUnit cu = parse(code);
        MethodDeclaration methodDeclaration = (MethodDeclaration) cu.getType(0).getMember(0);

        assertEquals(
                "return (Comparator<Map.Entry<K, V>> & Serializable) (c1, c2) -> c1.getKey().compareTo(c2.getKey());",
                print(methodDeclaration.getBody().get().getStatements().get(0)));
    }

    @Test
    void printClassWithoutJavaDocButWithComment() {
        String code = String.format(
                "/** javadoc */ public class A { %s// stuff%s}", LineSeparator.SYSTEM, LineSeparator.SYSTEM);
        CompilationUnit cu = parse(code);
        PrinterConfiguration ignoreJavaDoc = new DefaultPrinterConfiguration()
                .removeOption(new DefaultConfigurationOption(ConfigOption.PRINT_JAVADOC));
        String content = cu.toString(ignoreJavaDoc);
        assertEquals(
                String.format(
                        "public class A {%s    // stuff%s}%s",
                        LineSeparator.SYSTEM, LineSeparator.SYSTEM, LineSeparator.SYSTEM),
                content);
    }

    @Test
    void printImportsDefaultOrder() {
        String code = "import x.y.z;import a.b.c;import static b.c.d;class c {}";
        CompilationUnit cu = parse(code);
        String content = cu.toString();
        assertEqualsStringIgnoringEol(
                "import x.y.z;\n" + "import a.b.c;\n" + "import static b.c.d;\n" + "\n" + "class c {\n" + "}\n",
                content);
    }

    @Test
    void printImportsOrdered() {
        String code = "import x.y.z;import a.b.c;import static b.c.d;class c {}";
        CompilationUnit cu = parse(code);
        PrinterConfiguration orderImports =
                new DefaultPrinterConfiguration().addOption(new DefaultConfigurationOption(ConfigOption.ORDER_IMPORTS));
        String content = cu.toString(orderImports);
        assertEqualsStringIgnoringEol(
                "import static b.c.d;\n" + "import a.b.c;\n" + "import x.y.z;\n" + "\n" + "class c {\n" + "}\n",
                content);
    }

    @Test
    void multilineJavadocGetsFormatted() {
        CompilationUnit cu = new CompilationUnit();
        cu.addClass("X").addMethod("abc").setJavadocComment("line1\n   line2 *\n * line3");

        assertEqualsStringIgnoringEol(
                "public class X {\n" + "\n"
                        + "    /**\n"
                        + "     * line1\n"
                        + "     *    line2 *\n"
                        + "     *  line3\n"
                        + "     */\n"
                        + "    void abc() {\n"
                        + "    }\n"
                        + "}\n",
                cu.toString());
    }

    @Test
    void emptyJavadocGetsFormatted() {
        CompilationUnit cu = new CompilationUnit();
        cu.addClass("X").addMethod("abc").setJavadocComment("");

        assertEqualsStringIgnoringEol(
                "public class X {\n" + "\n" + "    /**\n" + "     */\n" + "    void abc() {\n" + "    }\n" + "}\n",
                cu.toString());
    }

    @Test
    void multilineJavadocWithLotsOfEmptyLinesGetsFormattedNeatly() {
        CompilationUnit cu = new CompilationUnit();
        cu.addClass("X").addMethod("abc").setJavadocComment("\n\n\n ab\n\n\n cd\n\n\n");

        assertEqualsStringIgnoringEol(
                "public class X {\n" + "\n"
                        + "    /**\n"
                        + "     * ab\n"
                        + "     *\n"
                        + "     * cd\n"
                        + "     */\n"
                        + "    void abc() {\n"
                        + "    }\n"
                        + "}\n",
                cu.toString());
    }

    @Test
    void singlelineJavadocGetsFormatted() {
        CompilationUnit cu = new CompilationUnit();
        cu.addClass("X").addMethod("abc").setJavadocComment("line1");

        assertEqualsStringIgnoringEol(
                "public class X {\n" + "\n"
                        + "    /**\n"
                        + "     * line1\n"
                        + "     */\n"
                        + "    void abc() {\n"
                        + "    }\n"
                        + "}\n",
                cu.toString());
    }

    @Test
    void javadocAlwaysGetsASpaceBetweenTheAsteriskAndTheRestOfTheLine() {
        CompilationUnit cu = new CompilationUnit();
        cu.addClass("X").addMethod("abc").setJavadocComment("line1\nline2");

        assertEqualsStringIgnoringEol(
                "public class X {\n" + "\n"
                        + "    /**\n"
                        + "     * line1\n"
                        + "     * line2\n"
                        + "     */\n"
                        + "    void abc() {\n"
                        + "    }\n"
                        + "}\n",
                cu.toString());
    }

    @Test
    void javadocAlwaysGetsAnAdditionalSpaceOrNeverGetsIt() {
        CompilationUnit cu = new CompilationUnit();
        cu.addClass("X").addMethod("abc").setJavadocComment("line1\n" + "line2\n" + "    3");

        assertEqualsStringIgnoringEol(
                "public class X {\n" + "\n"
                        + "    /**\n"
                        + "     * line1\n"
                        + "     * line2\n"
                        + "     *     3\n"
                        + "     */\n"
                        + "    void abc() {\n"
                        + "    }\n"
                        + "}\n",
                cu.toString());
    }

    @Test
    void singlelineCommentGetsFormatted() {
        CompilationUnit cu = new CompilationUnit();
        cu.addClass("X").addMethod("abc").setComment(new LineComment("   line1  \n "));

        assertEqualsStringIgnoringEol(
                "public class X {\n" + "\n" + "    //   line1\n" + "    void abc() {\n" + "    }\n" + "}\n",
                cu.toString());
    }

    @Test
    void blockcommentGetsNoFormatting() {
        CompilationUnit cu = parse("class A {\n" + "    public void helloWorld(String greeting, String name) {\n"
                + "        //sdfsdfsdf\n"
                + "            //sdfds\n"
                + "        /*\n"
                + "                            dgfdgfdgfdgfdgfd\n"
                + "         */\n"
                + "    }\n"
                + "}\n");

        assertEqualsStringIgnoringEol(
                "class A {\n" + "\n"
                        + "    public void helloWorld(String greeting, String name) {\n"
                        + "        //sdfsdfsdf\n"
                        + "        //sdfds\n"
                        + "        /*\n"
                        + "                            dgfdgfdgfdgfdgfd\n"
                        + "         */\n"
                        + "    }\n"
                        + "}\n",
                cu.toString());
    }

    private String expected = "public class SomeClass {\n" + "\n"
            + "    /**\n"
            + "     * tester line\n"
            + "     * multi line comment\n"
            + "     *   multi line comment\n"
            + "     * multi line comment\n"
            + "     *    multi line comment\n"
            + "     */\n"
            + "    public void add(int x, int y) {\n"
            + "    }\n"
            + "}\n";

    @Test
    void javadocIssue1907_allLeadingSpaces() {
        String input_allLeadingSpaces = "public class SomeClass{" + "/**\n"
                + " * tester line\n"
                + " * multi line comment\n"
                + " *   multi line comment\n"
                + "   * multi line comment\n"
                + "    multi line comment\n"
                + " */\n"
                + "public void add(int x, int y){}}";

        CompilationUnit cu_allLeadingSpaces = parse(input_allLeadingSpaces);
        assertEqualsStringIgnoringEol(expected, cu_allLeadingSpaces.toString());
    }

    @Test
    void javadocIssue1907_singleMissingLeadingSpace() {
        String input_singleMissingLeadingSpace = "public class SomeClass{" + "/**\n"
                + "* tester line\n"
                + " * multi line comment\n"
                + " *   multi line comment\n"
                + "   * multi line comment\n"
                + "    multi line comment\n"
                + " */\n"
                + "public void add(int x, int y){}}";

        CompilationUnit cu_singleMissingLeadingSpace = parse(input_singleMissingLeadingSpace);
        assertEqualsStringIgnoringEol(expected, cu_singleMissingLeadingSpace.toString());
    }

    @Test
    void javadocIssue1907_leadingTab() {
        String input_leadingTab = "public class SomeClass{" + "/**\n"
                + "\t * tester line\n"
                + " * multi line comment\n"
                + " *   multi line comment\n"
                + "   * multi line comment\n"
                + "    multi line comment\n"
                + " */\n"
                + "public void add(int x, int y){}}";

        CompilationUnit cu_leadingTab = parseCompilationUnit(input_leadingTab);
        assertEqualsStringIgnoringEol(expected, cu_leadingTab.toString());
    }

    @Test
    void printYield() {
        Statement statement = parseStatement("yield 5*5;");
        assertEqualsStringIgnoringEol("yield 5 * 5;", statement.toString());
    }

    @Test
    void printTextBlock() {
        CompilationUnit cu = parseCompilationUnit(
                ParserConfiguration.LanguageLevel.JAVA_13_PREVIEW,
                "class X{String html = \"\"\"\n" + "              <html>\n"
                        + "                  <body>\n"
                        + "                      <p>Hello, world</p>\n"
                        + "                  </body>\n"
                        + "              </html>\n"
                        + "              \"\"\";}");

        assertEqualsStringIgnoringEol(
                "String html = \"\"\"\n" + "    <html>\n"
                        + "        <body>\n"
                        + "            <p>Hello, world</p>\n"
                        + "        </body>\n"
                        + "    </html>\n"
                        + "    \"\"\";",
                cu.getClassByName("X").get().getFieldByName("html").get().toString());
    }

    @Test
    void printTextBlock2() {
        CompilationUnit cu = parseCompilationUnit(
                ParserConfiguration.LanguageLevel.JAVA_13_PREVIEW,
                "class X{String html = \"\"\"\n" + "              <html>\n" + "              </html>\"\"\";}");

        assertEqualsStringIgnoringEol(
                "String html = \"\"\"\n" + "    <html>\n" + "    </html>\"\"\";",
                cu.getClassByName("X").get().getFieldByName("html").get().toString());
    }

    @Test
    void innerClassWithConstructorReceiverParameterTest() {
        String innerClassWithConstructorReceiverParam = "public class A {\n\n" + "    class InnerA {\n\n"
                + "        InnerA(A A.this) {\n"
                + "        }\n"
                + "    }\n"
                + "}\n";
        CompilationUnit cu = parseCompilationUnit(innerClassWithConstructorReceiverParam);
        assertEqualsStringIgnoringEol(innerClassWithConstructorReceiverParam, print(cu));
    }

    @Test
    void printPermitsKeyworld() {
        CompilationUnit cu = parseCompilationUnit(
                ParserConfiguration.LanguageLevel.JAVA_17, "public sealed interface I1 permits I2, C, D {}");
        String expected = "public sealed interface I1 permits I2, C, D {\n" + "}\n";

        assertEqualsStringIgnoringEol(expected, cu.toString());
    }

    @Test
    public void testMarkdownComment() {
        String code = "class Foo {\n" + "\n"
                + "    /// This is a markdown comment\n"
                + "    /// for the foo method\n"
                + "    void foo(Integer arg) {\n"
                + "    }\n"
                + "}\n";

        CompilationUnit cu = parse(code);
        assertEqualsStringIgnoringEol(code, cu.toString());
    }

    @Test
    public void testModuleImport() {
        String code = "import module java.base;\n\n" + "class Foo {\n" + "}\n";

        CompilationUnit cu = parse(code);
        assertEqualsStringIgnoringEol(code, cu.toString());
    }

    @Test
    void printFlexibleConstructorBody() {
        String code = "public class A {\n" + "\n"
                + "    public A() {\n"
                + "        int x;\n"
                + "        super();\n"
                + "    }\n"
                + "}\n";
        CompilationUnit cu = parse(code);
        assertEqualsStringIgnoringEol(code, cu.toString());
    }

    @Test
    void printMinimalCompactClass() {
        String code = "void main() {\n" + "    System.out.println(\"Hello, World!\");\n" + "}\n";
        CompilationUnit cu = parse(code);
        assertEqualsStringIgnoringEol(code, cu.toString());
    }

    @Test
    void printCompactClassWithInstanceField() {
        String code = "int count = 0;\n" + "\n" + "void main() {\n" + "    count++;\n" + "}\n";
        CompilationUnit cu = parse(code);
        assertEqualsStringIgnoringEol(code, cu.toString());
    }

    @Test
    void printCompactClassWithMultipleMethods() {
        String code = "int add(int a, int b) {\n" + "    return a + b;\n" + "}\n" + "\n" + "void main() {\n" + "}\n";
        CompilationUnit cu = parse(code);
        assertEqualsStringIgnoringEol(code, cu.toString());
    }

    @Test
    void printCompactClassWithStaticAndInstanceMembers() {
        String code = "static final String GREETING = \"Hello\";\n"
                + "\n"
                + "String name = \"World\";\n"
                + "\n"
                + "static String formatMessage(String msg) {\n"
                + "    return msg.toUpperCase();\n"
                + "}\n"
                + "\n"
                + "void main() {\n"
                + "}\n";
        CompilationUnit cu = parse(code);
        assertEqualsStringIgnoringEol(code, cu.toString());
    }

    @Test
    void printCompactClassWithNestedClass() {
        String code = "class Inner {\n"
                + "\n"
                + "    void greet() {\n"
                + "        System.out.println(\"Hello from Inner\");\n"
                + "    }\n"
                + "}\n"
                + "\n"
                + "void main() {\n"
                + "    Inner inner = new Inner();\n"
                + "    inner.greet();\n"
                + "}\n";
        CompilationUnit cu = parse(code);
        assertEqualsStringIgnoringEol(code, cu.toString());
    }

    @Test
    void printCompactClassWithArrayField() {
        String code =
                "int[] numbers = { 1, 2, 3, 4, 5 };\n" + "\n" + "void main() {\n" + "    printNumbers();\n" + "}\n";
        CompilationUnit cu = parse(code);
        assertEqualsStringIgnoringEol(code, cu.toString());
    }

    @Test
    void printCompactClassWithGenericMethod() {
        String code = "<T> void printValue(T value) {\n"
                + "    System.out.println(\"Value: \" + value);\n"
                + "}\n"
                + "\n"
                + "void main() {\n"
                + "    printValue(\"String\");\n"
                + "    printValue(42);\n"
                + "    printValue(3.14);\n"
                + "}\n";
        CompilationUnit cu = parse(code);
        assertEqualsStringIgnoringEol(code, cu.toString());
    }

    @Test
    void printCompactClassWithRecord() {
        String code = "record Person(String name, int age) {\n"
                + "}\n"
                + "\n"
                + "void main() {\n"
                + "    Person p = new Person(\"Alice\", 30);\n"
                + "    System.out.println(p.name() + \" is \" + p.age() + \" years old\");\n"
                + "}\n";
        CompilationUnit cu = parse(code);
        assertEqualsStringIgnoringEol(code, cu.toString());
    }

    @Test
    void printCompactClassWithEnum() {
        String code = "enum Color {\n"
                + "\n"
                + "    RED, GREEN, BLUE\n"
                + "}\n"
                + "\n"
                + "void main() {\n"
                + "    for (Color c : Color.values()) {\n"
                + "        System.out.println(c);\n"
                + "    }\n"
                + "}\n";
        CompilationUnit cu = parse(code);
        assertEqualsStringIgnoringEol(code, cu.toString());
    }

    @Test
    void printCompactClassWithInterface() {
        String code = "interface Printer {\n"
                + "\n"
                + "    void print();\n"
                + "}\n"
                + "\n"
                + "class ConsolePrinter implements Printer {\n"
                + "\n"
                + "    public void print() {\n"
                + "        System.out.println(\"Printing...\");\n"
                + "    }\n"
                + "}\n"
                + "\n"
                + "void main() {\n"
                + "    Printer p = new ConsolePrinter();\n"
                + "    p.print();\n"
                + "}\n";
        CompilationUnit cu = parse(code);
        assertEqualsStringIgnoringEol(code, cu.toString());
    }

    @Test
    void printCompactClassWithVarargs() {
        String code = "int sum(int... numbers) {\n"
                + "    int total = 0;\n"
                + "    for (int n : numbers) {\n"
                + "        total += n;\n"
                + "    }\n"
                + "    return total;\n"
                + "}\n"
                + "\n"
                + "void main() {\n"
                + "    System.out.println(sum(1, 2, 3, 4, 5));\n"
                + "}\n";
        CompilationUnit cu = parse(code);
        assertEqualsStringIgnoringEol(code, cu.toString());
    }

    @Test
    void printCompactClassWithExceptionHandling() {
        String code = "void riskyOperation() throws Exception {\n"
                + "    throw new Exception(\"Something went wrong\");\n"
                + "}\n"
                + "\n"
                + "void main() {\n"
                + "    try {\n"
                + "        riskyOperation();\n"
                + "    } catch (Exception e) {\n"
                + "        System.out.println(\"Caught: \" + e.getMessage());\n"
                + "    }\n"
                + "}\n";
        CompilationUnit cu = parse(code);
        assertEqualsStringIgnoringEol(code, cu.toString());
    }

    @Test
    void printCompactClassWithAnnotationDeclaration() {
        String code = "@interface MyAnnotation {\n"
                + "\n"
                + "    String value() default \"\";\n"
                + "}\n"
                + "\n"
                + "void main() {\n"
                + "    System.out.println(\"Annotation declared\");\n"
                + "}\n";
        CompilationUnit cu = parse(code);
        assertEqualsStringIgnoringEol(code, cu.toString());
    }

    @Test
    void printCompactClassWithAnnotatedMethods() {
        String code = "@Deprecated\n"
                + "void oldMethod() {\n"
                + "    System.out.println(\"This is deprecated\");\n"
                + "}\n"
                + "\n"
                + "@Override\n"
                + "public String toString() {\n"
                + "    return \"AnnotatedMethod\";\n"
                + "}\n"
                + "\n"
                + "void main() {\n"
                + "    oldMethod();\n"
                + "    System.out.println(toString());\n"
                + "}\n";
        CompilationUnit cu = parse(code);
        assertEqualsStringIgnoringEol(code, cu.toString());
    }

    @Test
    void printCompactClassWithCustomAnnotationAndAnnotatedMethods() {
        String code = "@interface Author {\n"
                + "\n"
                + "    String name();\n"
                + "}\n"
                + "\n"
                + "@Override\n"
                + "int calculate(int x) {\n"
                + "    return x * 2;\n"
                + "}\n"
                + "\n"
                + "void main() {\n"
                + "}\n";
        CompilationUnit cu = parse(code);
        assertEqualsStringIgnoringEol(code, cu.toString());
    }
}
