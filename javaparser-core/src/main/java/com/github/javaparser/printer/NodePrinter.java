package com.github.javaparser.printer;

import com.github.javaparser.ast.Node;

public interface NodePrinter {

    String asString(Node node);
}
