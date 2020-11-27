package com.github.javaparser.printer;

import com.github.javaparser.ast.Node;

public interface Printable {

    String print(Node node);

}