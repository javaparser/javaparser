package com.github.javaparser.printer;

import com.github.javaparser.ast.Node;

/**
 * Pretty printer for AST nodes.
 */
public class PrettyPrinter {
    private final PrettyPrinterConfiguration configuration;

    public PrettyPrinter(PrettyPrinterConfiguration configuration) {
        this.configuration = configuration;
    }

    public String print(Node node) {
        final PrettyPrintVisitor visitor = new PrettyPrintVisitor(configuration);
        node.accept(visitor, null);
        return visitor.getSource();
    }
}
