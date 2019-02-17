package com.github.javaparser.ast;

import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parse;
import static com.github.javaparser.StaticJavaParser.parsePackageDeclaration;
import static com.github.javaparser.utils.Utils.EOL;
import static org.junit.jupiter.api.Assertions.assertEquals;

class ReplaceNodeTest {
    @Test
    void testSimplePropertyWithGenericReplace() {
        CompilationUnit cu = parse("package x; class Y {}");
        cu.replace(cu.getPackageDeclaration().get(), parsePackageDeclaration("package z;"));
        assertEquals(String.format("package z;%1$s" +
                "%1$s" +
                "class Y {%1$s" +
                "}%1$s", EOL), cu.toString());
    }

    @Test
    void testListProperty() {
        CompilationUnit cu = parse("package x; class Y {}");
        cu.replace(cu.getClassByName("Y").get(), parse("class B{int y;}").getClassByName("B").get());
        assertEquals(String.format("package x;%1$s" +
                "%1$s" +
                "class B {%1$s" +
                "%1$s" +
                "    int y;%1$s" +
                "}%1$s", EOL), cu.toString());
    }
}
