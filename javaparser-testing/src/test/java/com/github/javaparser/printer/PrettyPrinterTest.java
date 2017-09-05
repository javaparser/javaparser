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
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

import java.util.stream.IntStream;

public class PrettyPrinterTest {

    private String prettyPrintField(String code) {
        CompilationUnit cu = JavaParser.parse(code);
        return new PrettyPrinter().print(cu.getChildNodesByType(FieldDeclaration.class).get(0));
    }

    private String prettyPrintVar(String code) {
        CompilationUnit cu = JavaParser.parse(code);
        return new PrettyPrinter().print(cu.getChildNodesByType(VariableDeclarationExpr.class).get(0));
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
        CompilationUnit cu = JavaParser.parse(code);
        PrettyPrinter printer = new PrettyPrinter(new PrettyPrinterConfiguration().setVisitorFactory(TestVisitor::new));
        return printer.print(cu.getChildNodesByType(ClassOrInterfaceDeclaration.class).get(0));
    }

    @Test
    public void printUseTestVisitor(){
        String code;
        code = "class A { void foo(){ int a, b[]; }}";
        assertEquals("test", prettyPrintConfigurable(code));
    }
    
    @Test
    public void prettyColumnAlignParameters_enabled() {
        PrettyPrinterConfiguration config = new PrettyPrinterConfiguration();
        config.setIndent("\t");
        config.setColumnAlignParameters(true);
        
        final String EOL = config.getEndOfLineCharacter();
        
        String code = "class Example { void foo(Object arg0,Object arg1){ myMethod(1, 2, 3, 5, Object.class); } }";
        String expected = "class Example {" + EOL + 
                "" + EOL + 
                "\tvoid foo(Object arg0, Object arg1) {" + EOL + 
                "\t\tmyMethod(1," + EOL + 
                "\t\t         2," + EOL + 
                "\t\t         3," + EOL + 
                "\t\t         5," + EOL + 
                "\t\t         Object.class);" + EOL + 
                "\t}" + EOL + 
                "}" + EOL + 
                "";
        
        assertEquals(expected, new PrettyPrinter(config).print(JavaParser.parse(code)));
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
        
        assertEquals(expected, new PrettyPrinter(config).print(JavaParser.parse(code)));
    }
    
    @Test
    public void prettyAlignMethodCallChains_enabled() {
        PrettyPrinterConfiguration config = new PrettyPrinterConfiguration();
        config.setIndent("\t");
        config.setColumnAlignFirstMethodChain(true);
        
        final String EOL = config.getEndOfLineCharacter();
        
        String code = "class Example { void foo() { IntStream.range(0, 10).filter(x -> x % 2 == 0).map(x -> x * IntStream.of(1,3,5,1).sum()).forEach(System.out::println); } }";
        String expected = "class Example {" + EOL + 
                "" + EOL + 
                "\tvoid foo() {" + EOL + 
                "\t\tIntStream.range(0, 10)" + EOL + 
                "\t\t         .filter(x -> x % 2 == 0)" + EOL + 
                "\t\t         .map(x -> x * IntStream.of(1, 3, 5, 1)" + EOL + 
                "\t\t                                .sum())" + EOL + 
                "\t\t         .forEach(System.out::println);" + EOL + 
                "\t}" + EOL + 
                "}" + EOL + 
                "";

        assertEquals(expected, new PrettyPrinter(config).print(JavaParser.parse(code)));
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

        assertEquals(expected, new PrettyPrinter(config).print(JavaParser.parse(code)));
    }

}
