package com.github.javaparser.ast;

import org.junit.Test;

import static com.github.javaparser.JavaParser.parse;
import static com.github.javaparser.JavaParser.parsePackageDeclaration;
import static org.junit.Assert.assertEquals;

public class ReplaceNodeTest {
    @Test
    public void testSimplePropertyWithDedicatedReplace() {
        CompilationUnit cu = parse("package x; class Y {}");
        cu.replacePackageDeclaration(parsePackageDeclaration("package z;"));
        assertEquals("package z;\n" +
                "\n" +
                "class Y {\n" +
                "}\n", cu.toString());
    }

    @Test
    public void testSimplePropertyWithGenericReplace() {
        CompilationUnit cu = parse("package x; class Y {}");
        cu.replace(cu.getPackageDeclaration().get(), parsePackageDeclaration("package z;"));
        assertEquals("package z;\n" +
                "\n" +
                "class Y {\n" +
                "}\n", cu.toString());
    }

    @Test
    public void testListProperty() {
        CompilationUnit cu = parse("package x; class Y {}");
        cu.replace(cu.getClassByName("Y").get(), parse("class B{int y;}").getClassByName("B").get());
        assertEquals("package x;\n" +
                "\n" +
                "class B {\n" +
                "\n" +
                "    int y;\n" +
                "}\n", cu.toString());
    }
}
