package com.github.javaparser;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.Expression;

public class Xxxxxxxxxxxxxxxxxxxxxxx {
    public static void main(String[] args) {
        Node n= JavaParser.parse("class X { void x() {interface Y { } } }");
        
        System.out.println(n);
    }
}
