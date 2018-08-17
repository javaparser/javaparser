package com.github.javaparser.ast;

import org.junit.Test;

import static com.github.javaparser.JavaParser.getInternalParser;
import static com.github.javaparser.utils.Utils.EOL;
import static org.junit.Assert.assertEquals;

public class ReplaceNodeTest {
    @Test
    public void testSimplePropertyWithGenericReplace() {
        CompilationUnit cu = getInternalParser().parse("package x; class Y {}");
        cu.replace(cu.getPackageDeclaration().get(), getInternalParser().parsePackageDeclaration("package z;"));
        assertEquals(String.format("package z;%1$s" +
                "%1$s" +
                "class Y {%1$s" +
                "}%1$s", EOL), cu.toString());
    }

    @Test
    public void testListProperty() {
        CompilationUnit cu = getInternalParser().parse("package x; class Y {}");
        cu.replace(cu.getClassByName("Y").get(), getInternalParser().parse("class B{int y;}").getClassByName("B").get());
        assertEquals(String.format("package x;%1$s" +
                "%1$s" +
                "class B {%1$s" +
                "%1$s" +
                "    int y;%1$s" +
                "}%1$s", EOL), cu.toString());
    }
}
