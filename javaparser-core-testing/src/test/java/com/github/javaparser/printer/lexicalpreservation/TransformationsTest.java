/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.NullLiteralExpr;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.PrimitiveType;
import org.junit.jupiter.api.Test;

import java.io.IOException;

import static com.github.javaparser.ast.Modifier.Keyword.STATIC;
import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;
import static com.github.javaparser.utils.Utils.SYSTEM_EOL;

/**
 * These tests are more "high level" than the ones in LexicalPreservingPrinterTest.
 * The idea is to perform some transformations on the code, print it back and see if the generated code
 * is the expected one. We do not care about the internal state of LexicalPreservingPrinter, just the visible result.
 */
class TransformationsTest extends  AbstractLexicalPreservingTest {

    @Test
    void unchangedSimpleClasses() throws IOException {
        assertUnchanged("Example1");
        assertUnchanged("Example2");
    }

    @Test
    void unchangedComplexFile() throws IOException {
        assertUnchanged("Example4");
    }

    @Test
    void example1() throws IOException {
        considerExample("Example1_original");
        cu.getClassByName("A").get().getFieldByName("a").get().setModifiers(STATIC);
        assertTransformed("Example1", cu);
    }

    @Test
    void example2() throws IOException {
        considerExample("Example2_original");
        cu.getClassByName("A").get().getFieldByName("a").get().getVariable(0).setInitializer("10");
        assertTransformed("Example2", cu);
    }

    @Test
    void example3() throws IOException {
        considerExample("Example3_original");
        cu.getClassByName("A").get().getFieldByName("a").get().getVariable(0).setInitializer((Expression) null);
        assertTransformed("Example3", cu);
    }

    @Test
    void example5() throws IOException {
        considerExample("Example5_original");
        cu.getClassByName("A").get().getFieldByName("a").get().getVariable(0).setInitializer(new NullLiteralExpr());
        assertTransformed("Example5", cu);
    }

    @Test
    void example6() throws IOException {
        considerExample("Example6_original");
        cu.getClassByName("A").get().getFieldByName("a").get().getVariable(0).setName("someOtherName");
        assertTransformed("Example6", cu);
    }

    @Test
    void example7() throws IOException {
        considerExample("Example7_original");
        cu.getClassByName("A").get().getFieldByName("a").get().getVariable(0).setType(new ArrayType(PrimitiveType.intType()));
        assertTransformed("Example7", cu);
    }

    @Test
    void example8() throws IOException {
        considerExample("Example8_original");
        FieldDeclaration fd = cu.getClassByName("A").get().getMember(0).asFieldDeclaration();
        fd.addVariable(new VariableDeclarator(PrimitiveType.intType(), "b"));
        assertTransformed("Example8", cu);
    }

    @Test
    void example9() throws IOException {
        considerExample("Example9_original");
        FieldDeclaration fd = cu.getClassByName("A").get().getMember(0).asFieldDeclaration();
        fd.addVariable(new VariableDeclarator(new ArrayType(PrimitiveType.intType()), "b"));
        assertTransformed("Example9", cu);
    }

    @Test
    void example10() throws IOException {
        considerExample("Example10_original");
        cu.getClassByName("A").get().getMembers().remove(0);
        assertTransformed("Example10", cu);
    }

    @Test
    void exampleParam1() throws IOException {
        considerExample("Example_param1_original");
        MethodDeclaration md = cu.getClassByName("A").get().getMember(0).asMethodDeclaration();
        md.addParameter("int", "p1");
        assertTransformed("Example_param1", cu);
    }

    @Test
    void exampleParam2() throws IOException {
        considerExample("Example_param1_original");
        MethodDeclaration md = cu.getClassByName("A").get().getMember(0).asMethodDeclaration();
        md.addParameter(new ArrayType(PrimitiveType.intType()), "p1");
        md.addParameter("char", "p2");
        assertTransformed("Example_param2", cu);
    }

    @Test
    void exampleParam3() throws IOException {
        considerExample("Example_param3_original");
        MethodDeclaration md = cu.getClassByName("A").get().getMember(0).asMethodDeclaration();
        md.getParameters().remove(0);
        assertTransformed("Example_param3", cu);
    }

    @Test
    void exampleParam4() throws IOException {
        considerExample("Example_param3_original");
        MethodDeclaration md = cu.getClassByName("A").get().getMember(0).asMethodDeclaration();
        md.getParameters().remove(1);
        assertTransformed("Example_param4", cu);
    }

    @Test
    void exampleParam5() throws IOException {
        considerExample("Example_param3_original");
        MethodDeclaration md = cu.getClassByName("A").get().getMember(0).asMethodDeclaration();
        md.setType(PrimitiveType.intType());
        assertTransformed("Example_param5b", cu);
        md.getBody().get().getStatements().add(new ReturnStmt(new NameExpr("p1")));
        String expected = readExample("Example_param5" + "_expected");
        String s = LexicalPreservingPrinter.print(cu);
        assertEqualsStringIgnoringEol(expected, s);
    }

    @Test
    void issue2099AddingStatementAfterTraillingComment1() {
        considerStatement(
                "    if(value != null) {" + SYSTEM_EOL +
                "        value.value();" + SYSTEM_EOL +
                "    }");

        BlockStmt blockStmt = LexicalPreservingPrinter.setup(StaticJavaParser.parseBlock("{" + SYSTEM_EOL +
                "       value1();" + SYSTEM_EOL +
                "    value2(); // Test" + SYSTEM_EOL +
                "}"));

        blockStmt.addStatement(statement);
        String s = LexicalPreservingPrinter.print(blockStmt);
        String expected = "{\n" +
                "       value1();\n" +
                "    value2(); // Test\n" +
                "    if(value != null) {\n" +
                "        value.value();\n" +
                "    }\n" +
                "}";
        assertEqualsStringIgnoringEol(expected, s);
    }

    @Test
    void issue2099AddingStatementAfterTraillingComment2() {
        considerStatement(
                "    if(value != null) {" + SYSTEM_EOL +
                "        value.value();" + SYSTEM_EOL +
                "    }");

        BlockStmt blockStmt = LexicalPreservingPrinter.setup(StaticJavaParser.parseBlock("{" + SYSTEM_EOL +
                "       value1();" + SYSTEM_EOL +
                "    value2(); /* test */" + SYSTEM_EOL +
                "}"));

        blockStmt.addStatement(statement);
        String s = LexicalPreservingPrinter.print(blockStmt);
        String expected = "{\n" +
                "       value1();\n" +
                "    value2(); /* test */\n" +
                "    if(value != null) {\n" +
                "        value.value();\n" +
                "    }\n" +
                "}";
        assertEqualsStringIgnoringEol(expected, s);
    }


    @Test
    void addingStatement1() {
        considerStatement(
                "        if(value != null) {" + SYSTEM_EOL +
                        "            value.value();" + SYSTEM_EOL +
                        "        }");

        CompilationUnit compilationUnit = LexicalPreservingPrinter.setup(StaticJavaParser.parse("public class Test {" + SYSTEM_EOL +
                "    public void method() {" + SYSTEM_EOL +
                "           value1();" + SYSTEM_EOL +
                "        value2(); // Test" + SYSTEM_EOL +
                "    }" + SYSTEM_EOL +
                "}"));
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = (ClassOrInterfaceDeclaration)compilationUnit.getChildNodes().get(0);
        MethodDeclaration methodDeclaration = (MethodDeclaration)classOrInterfaceDeclaration.getChildNodes().get(2);
        methodDeclaration.getBody().get().addStatement(statement);

        String s = LexicalPreservingPrinter.print(compilationUnit);
        String expected = "public class Test {\n" +
                "    public void method() {\n" +
                "           value1();\n" +
                "        value2(); // Test\n" +
                "        if(value != null) {\n" +
                "            value.value();\n" +
                "        }\n" +
                "    }\n" +
                "}";
        assertEqualsStringIgnoringEol(expected, s);
    }

    @Test
    void addingStatement2() {
        considerStatement(
                "        if(value != null) {" + SYSTEM_EOL +
                        "            value.value();" + SYSTEM_EOL +
                        "        }");

        CompilationUnit compilationUnit = LexicalPreservingPrinter.setup(StaticJavaParser.parse("public class Test {" + SYSTEM_EOL +
                "    public void method() {" + SYSTEM_EOL +
                "           value1();" + SYSTEM_EOL +
                "        value2();" + SYSTEM_EOL +
                "    }" + SYSTEM_EOL +
                "}"));
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = (ClassOrInterfaceDeclaration)compilationUnit.getChildNodes().get(0);
        MethodDeclaration methodDeclaration = (MethodDeclaration)classOrInterfaceDeclaration.getChildNodes().get(2);
        methodDeclaration.getBody().get().addStatement(statement);

        String s = LexicalPreservingPrinter.print(compilationUnit);
        String expected = "public class Test {\n" +
                "    public void method() {\n" +
                "           value1();\n" +
                "        value2();\n" +
                "        if(value != null) {\n" +
                "            value.value();\n" +
                "        }\n" +
                "    }\n" +
                "}";
        assertEqualsStringIgnoringEol(expected, s);
    }

    @Test
    void addingStatement3() {
        considerStatement(
                "        if(value != null) {" + SYSTEM_EOL +
                        "            value.value();" + SYSTEM_EOL +
                        "        }");

        CompilationUnit compilationUnit = LexicalPreservingPrinter.setup(StaticJavaParser.parse("public class Test {" + SYSTEM_EOL +
                "    public void method() {" + SYSTEM_EOL +
                "           value1();" + SYSTEM_EOL +
                "        value2();" + SYSTEM_EOL + SYSTEM_EOL +
                "    }" + SYSTEM_EOL +
                "}"));
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = (ClassOrInterfaceDeclaration)compilationUnit.getChildNodes().get(0);
        MethodDeclaration methodDeclaration = (MethodDeclaration)classOrInterfaceDeclaration.getChildNodes().get(2);
        methodDeclaration.getBody().get().addStatement(statement);

        String s = LexicalPreservingPrinter.print(compilationUnit);
        String expected = "public class Test {\n" +
                "    public void method() {\n" +
                "           value1();\n" +
                "        value2();\n" +
                "        if(value != null) {\n" +
                "            value.value();\n" +
                "        }\n\n" +
                "    }\n" +
                "}";
        assertEqualsStringIgnoringEol(expected, s);
    }
    
    @Test
    void removingInSingleMemberList() {
        considerCode(
                "class A {\n" +
                "    int a;\n" +
                "}");
        cu.getClassByName("A").get().getMembers().remove(0);
        String expected = 
                "class A {\n" +
                "}";
        String s = LexicalPreservingPrinter.print(cu);
        assertEqualsStringIgnoringEol(expected, s);
    }
    
    @Test
    void removingInMultiMembersList() {
        considerCode(
                "class A {\n" +
                "    int a;\n" +
                "    int b;\n" +
                "}");
        cu.getClassByName("A").get().getMembers().removeLast();
        String expected = 
                "class A {\n" +
                "    int a;\n" +
                "}";
        String s = LexicalPreservingPrinter.print(cu);
        assertEqualsStringIgnoringEol(expected, s);
    }
    
    
}
