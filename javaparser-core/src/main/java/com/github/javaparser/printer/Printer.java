package com.github.javaparser.printer;

import com.github.javaparser.ast.Node;
import com.github.javaparser.printer.configuration.ConfigurationPrinter;

/**
 * Printer interface defines the API for a printer.
 * A printer outputs the AST as formatted Java source code. 
 *
 */
public interface Printer {

    String print(Node node);

    Printer setConfiguration(ConfigurationPrinter configuration);
    
    ConfigurationPrinter getConfiguration();

}