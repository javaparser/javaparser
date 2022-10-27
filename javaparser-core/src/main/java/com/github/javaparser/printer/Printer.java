package com.github.javaparser.printer;

import com.github.javaparser.ast.Node;
import com.github.javaparser.printer.configuration.PrinterConfiguration;

/**
 * Printer interface defines the API for a printer.
 * A printer outputs the AST as formatted Java source code. 
 *
 */
public interface Printer {

    String print(Node node);

    Printer setConfiguration(PrinterConfiguration configuration);
    
    PrinterConfiguration getConfiguration();

}