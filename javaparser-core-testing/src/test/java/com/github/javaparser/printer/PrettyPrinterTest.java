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
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.type.PrimitiveType;
import org.junit.Test;

import static com.github.javaparser.JavaParser.parse;
import static com.github.javaparser.JavaParser.parseBodyDeclaration;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.JAVA_9;
import static com.github.javaparser.printer.PrettyPrinterConfiguration.IndentType.TABS;
import static com.github.javaparser.printer.PrettyPrinterConfiguration.IndentType.TABS_WITH_SPACE_ALIGN;
import static com.github.javaparser.utils.TestUtils.assertEqualsNoEol;
import static org.junit.Assert.assertEquals;

public class PrettyPrinterTest {

    private String prettyPrintField(String code) {
        CompilationUnit cu = parse(code);
        return new PrettyPrinter().print(cu.findFirst(FieldDeclaration.class).get());
    }

    private String prettyPrintVar(String code) {
        CompilationUnit cu = parse(code);
        return new PrettyPrinter().print(cu.findAll(VariableDeclarationExpr.class).get(0));
    }

    @Test
    public void printingArrayFields() {
        String code;
        code = "class A { int a, b[]; }";
        assertEquals("int a, b[];", prettyPrintField(code));

        code = "class A { int[] a[], b[]; }";
        assertEquals("int[][] a, b;", prettyPrintField(code));

        code = "class A { int[] a[][], b; }";
        assertEquals("int[] a[][], b;", prettyPrintField(code));

        code = "class A { int[] a, b; }";
        assertEquals("int[] a, b;", prettyPrintField(code));

        code = "class A { int a[], b[]; }";
        assertEquals("int[] a, b;", prettyPrintField(code));
    }

    @Test
    public void printingArrayVariables() {
        String code;
        code = "class A { void foo(){ int a, b[]; }}";
        assertEquals("int a, b[]", prettyPrintVar(code));

        code = "class A { void foo(){ int[] a[], b[]; }}";
        assertEquals("int[][] a, b", prettyPrintVar(code));

        code = "class A { void foo(){ int[] a[][], b; }}";
        assertEquals("int[] a[][], b", prettyPrintVar(code));

        code = "class A { void foo(){ int[] a, b; }}";
        assertEquals("int[] a, b", prettyPrintVar(code));

        code = "class A { void foo(){ int a[], b[]; }}";
        assertEquals("int[] a, b", prettyPrintVar(code));
    }

    private String prettyPrintConfigurable(String code) {
        CompilationUnit cu = parse(code);
        PrettyPrinter printer = new PrettyPrinter(new PrettyPrinterConfiguration().setVisitorFactory(TestVisitor::new));
        return printer.print(cu.findFirst(ClassOrInterfaceDeclaration.class).get());
    }

    @Test
    public void printUseTestVisitor() {
        String code;
        code = "class A { void foo(){ int a, b[]; }}";
        assertEquals("test", prettyPrintConfigurable(code));
    }

    @Test
    public void prettyColumnAlignParameters_enabled() {
        PrettyPrinterConfiguration config = new PrettyPrinterConfiguration()
                .setColumnAlignParameters(true);

        final String EOL = config.getEndOfLineCharacter();

        String code = "class Example { void foo(Object arg0,Object arg1){ myMethod(1, 2, 3, 5, Object.class); } }";
        String expected = "class Example {" + EOL +
                "" + EOL +
                "    void foo(Object arg0, Object arg1) {" + EOL +
                "        myMethod(1," + EOL +
                "                 2," + EOL +
                "                 3," + EOL +
                "                 5," + EOL +
                "                 Object.class);" + EOL +
                "    }" + EOL +
                "}" + EOL +
                "";

        assertEquals(expected, new PrettyPrinter(config).print(parse(code)));
    }

    @Test
    public void prettyColumnAlignParameters_disabled() {
        PrettyPrinterConfiguration config = new PrettyPrinterConfiguration();
        final String EOL = config.getEndOfLineCharacter();

        String code = "class Example { void foo(Object arg0,Object arg1){ myMethod(1, 2, 3, 5, Object.class); } }";
        String expected = "class Example {" + EOL +
                "" + EOL +
                "    void foo(Object arg0, Object arg1) {" + EOL +
                "        myMethod(1, 2, 3, 5, Object.class);" + EOL +
                "    }" + EOL +
                "}" + EOL +
                "";

        assertEquals(expected, new PrettyPrinter(config).print(parse(code)));
    }

    @Test
    public void prettyAlignMethodCallChains_enabled() {
        PrettyPrinterConfiguration config = new PrettyPrinterConfiguration()
                .setColumnAlignFirstMethodChain(true);

        final String EOL = config.getEndOfLineCharacter();

        String code = "class Example { void foo() { IntStream.range(0, 10).filter(x -> x % 2 == 0).map(x -> x * IntStream.of(1,3,5,1).sum()).forEach(System.out::println); } }";
        String expected = "class Example {" + EOL +
                "" + EOL +
                "    void foo() {" + EOL +
                "        IntStream.range(0, 10)" + EOL +
                "                 .filter(x -> x % 2 == 0)" + EOL +
                "                 .map(x -> x * IntStream.of(1, 3, 5, 1)" + EOL +
                "                                        .sum())" + EOL +
                "                 .forEach(System.out::println);" + EOL +
                "    }" + EOL +
                "}" + EOL +
                "";

        assertEquals(expected, new PrettyPrinter(config).print(parse(code)));
    }

    @Test
    public void prettyAlignMethodCallChains_disabled() {
        PrettyPrinterConfiguration config = new PrettyPrinterConfiguration();
        final String EOL = config.getEndOfLineCharacter();

        String code = "class Example { void foo() { IntStream.range(0, 10).filter(x -> x % 2 == 0).map(x -> x * IntStream.of(1,3,5,1).sum()).forEach(System.out::println); } }";
        String expected = "class Example {" + EOL +
                "" + EOL +
                "    void foo() {" + EOL +
                "        IntStream.range(0, 10).filter(x -> x % 2 == 0).map(x -> x * IntStream.of(1, 3, 5, 1).sum()).forEach(System.out::println);" + EOL +
                "    }" + EOL +
                "}" + EOL +
                "";

        assertEquals(expected, new PrettyPrinter(config).print(parse(code)));
    }

    @Test
    public void enumConstantsHorizontally() {
        CompilationUnit cu = parse("enum X{A, B, C, D, E}");
        assertEqualsNoEol("enum X {\n\n    A, B, C, D, E\n}\n", new PrettyPrinter().print(cu));
    }

    @Test
    public void enumConstantsVertically() {
        CompilationUnit cu = parse("enum X{A, B, C, D, E, F}");
        assertEqualsNoEol("enum X {\n\n    A,\n    B,\n    C,\n    D,\n    E,\n    F\n}\n", new PrettyPrinter().print(cu));
    }

    @Test
    public void printingInconsistentVariables() {
        FieldDeclaration fieldDeclaration = parseBodyDeclaration("int a, b;").asFieldDeclaration();

        assertEquals("int a, b;", fieldDeclaration.toString());

        fieldDeclaration.getVariable(0).setType(PrimitiveType.doubleType());

        assertEquals("??? a, b;", fieldDeclaration.toString());

        fieldDeclaration.getVariable(1).setType(PrimitiveType.doubleType());

        assertEquals("double a, b;", fieldDeclaration.toString());
    }

    @Test
    public void prettyAlignMethodCallChainsIndentsArgumentsWithBlocksCorrectly() {

        CompilationUnit cu = JavaParser.parse("class Foo { void bar() { foo().bar().baz(() -> { boo().baa().bee(); }).bam(); } }");
        String printed = new PrettyPrinter(new PrettyPrinterConfiguration().setColumnAlignFirstMethodChain(true))
                .print(cu);

        assertEqualsNoEol("class Foo {\n" +
                "\n" +
                "    void bar() {\n" +
                "        foo().bar()\n" +
                "             .baz(() -> {\n" +
                "                 boo().baa()\n" +
                "                      .bee();\n" +
                "             })\n" +
                "             .bam();\n" +
                "    }\n" +
                "}\n", printed);
    }

    @Test
    public void indentWithTabsAsFarAsPossible() {

        CompilationUnit cu = JavaParser.parse("class Foo { void bar() { foo().bar().baz(() -> { boo().baa().bees(a, b, c); }).bam(); } }");
        String printed = new PrettyPrinter(new PrettyPrinterConfiguration()
                .setColumnAlignFirstMethodChain(true)
                .setColumnAlignParameters(true)
                .setIndentType(TABS)
                .setIndentSize(1))
                .print(cu);

        assertEqualsNoEol("class Foo {\n" +
                "\n" +
                "\tvoid bar() {\n" +
                "\t\tfoo().bar()\n" +
                "\t\t\t .baz(() -> {\n" +
                "\t\t\t\t\t  boo().baa()\n" +
                "\t\t\t\t\t\t   .bees(a,\n" +
                "\t\t\t\t\t\t\t\t b,\n" +
                "\t\t\t\t\t\t\t\t c);\n" +
                "\t\t\t\t  })\n" +
                "\t\t\t .bam();\n" +
                "\t}\n" +
                "}\n", printed);
    }

    @Test
    public void indentWithTabsAlignWithSpaces() {

        CompilationUnit cu = JavaParser.parse("class Foo { void bar() { foo().bar().baz(() -> { boo().baa().bee(a, b, c); }).bam(); } }");
        String printed = new PrettyPrinter(new PrettyPrinterConfiguration()
                .setColumnAlignFirstMethodChain(true)
                .setColumnAlignParameters(true)
                .setIndentType(TABS_WITH_SPACE_ALIGN)
                .setIndentSize(1))
                .print(cu);

        assertEqualsNoEol("class Foo {\n" +
                "\n" +
                "\tvoid bar() {\n" +
                "\t\tfoo().bar()\n" +
                "\t\t     .baz(() -> {\n" +
                "\t\t          \tboo().baa()\n" +
                "\t\t          \t     .bee(a,\n" +
                "\t\t          \t          b,\n" +
                "\t\t          \t          c);\n" +
                "\t\t          })\n" +
                "\t\t     .bam();\n" +
                "\t}\n" +
                "}\n", printed);
    }

    @Test
    public void printAnnotationsAtPrettyPlaces() {

        JavaParser.getStaticConfiguration().setLanguageLevel(JAVA_9);
        CompilationUnit cu = JavaParser.parse("@Documented\n" +
                "@Repeatable\n" +
                "package com.github.javaparser;\n" +
                "\n" +
                "import java.lang.annotation.Documented;\n" +
                "import java.lang.annotation.Repeatable;\n" +
                "\n" +
                "@Documented\n" +
                "@Repeatable\n" +
                "@interface Annotation {\n" +
                "\n" +
                "    @Documented\n" +
                "    @Repeatable\n" +
                "    String value();\n" +
                "}\n" +
                "\n" +
                "@Documented\n" +
                "@Repeatable\n" +
                "class Class<@Documented @Repeatable T> {\n" +
                "\n" +
                "    @Documented\n" +
                "    @Repeatable\n" +
                "    byte b;\n" +
                "\n" +
                "    @Documented\n" +
                "    @Repeatable\n" +
                "    Class(@Documented @Repeatable int i) {\n" +
                "        @Documented\n" +
                "        @Repeatable\n" +
                "        short s;\n" +
                "    }\n" +
                "\n" +
                "    @Documented\n" +
                "    @Repeatable\n" +
                "    void method(@Documented @Repeatable Class this) {\n" +
                "        for (@Deprecated int i : arr4[0]) {\n" +
                "            x--;\n" +
                "        }\n" +
                "    }\n" +
                "\n" +
                "    void method(@Documented @Repeatable Class this, int i) {\n" +
                "    }\n" +
                "}\n" +
                "\n" +
                "@Documented\n" +
                "@Repeatable\n" +
                "enum Foo {\n" +
                "\n" +
                "    @Documented\n" +
                "    @Repeatable\n" +
                "    BAR\n" +
                "}\n" +
                "@Documented\n" +
                "@Repeatable\n" +
                "module foo.bar {\n" +
                "}\n");

        String printed = new PrettyPrinter().print(cu);

        assertEqualsNoEol("@Documented\n" +
                "@Repeatable\n" +
                "package com.github.javaparser;\n" +
                "\n" +
                "import java.lang.annotation.Documented;\n" +
                "import java.lang.annotation.Repeatable;\n" +
                "\n" +
                "@Documented\n" +
                "@Repeatable\n" +
                "@interface Annotation {\n" +
                "\n" +
                "    @Documented\n" +
                "    @Repeatable\n" +
                "    String value();\n" +
                "}\n" +
                "\n" +
                "@Documented\n" +
                "@Repeatable\n" +
                "class Class<@Documented @Repeatable T> {\n" +
                "\n" +
                "    @Documented\n" +
                "    @Repeatable\n" +
                "    byte b;\n" +
                "\n" +
                "    @Documented\n" +
                "    @Repeatable\n" +
                "    Class(@Documented @Repeatable int i) {\n" +
                "        @Documented\n" +
                "        @Repeatable\n" +
                "        short s;\n" +
                "    }\n" +
                "\n" +
                "    @Documented\n" +
                "    @Repeatable\n" +
                "    void method(@Documented @Repeatable Class this) {\n" +
                "        for (@Deprecated int i : arr4[0]) {\n" +
                "            x--;\n" +
                "        }\n" +
                "    }\n" +
                "\n" +
                "    void method(@Documented @Repeatable Class this, int i) {\n" +
                "    }\n" +
                "}\n" +
                "\n" +
                "@Documented\n" +
                "@Repeatable\n" +
                "enum Foo {\n" +
                "\n" +
                "    @Documented\n" +
                "    @Repeatable\n" +
                "    BAR\n" +
                "}\n" +
                "@Documented\n" +
                "@Repeatable\n" +
                "module foo.bar {\n" +
                "}\n", printed);
    }
}
