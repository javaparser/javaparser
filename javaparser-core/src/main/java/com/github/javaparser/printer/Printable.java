package com.github.javaparser.printer;

import com.github.javaparser.ast.Node;
import com.github.javaparser.printer.configuration.ConfigurablePrinter;

/**
 * Printable interface defines the API for a printer.
 * A printer outputs the AST as formatted Java source code. 
 *
 */
public interface Printable {

    String print(Node node);

    Printable setConfiguration(ConfigurablePrinter configuration);
    
    ConfigurablePrinter getConfiguration();

}