package com.github.javaparser.printer;

import com.github.javaparser.ast.Node;
import com.github.javaparser.printer.configuration.ConfigurablePrinter;

public interface Printable {

    String print(Node node);

    Printable setConfiguration(ConfigurablePrinter configuration);
    
    ConfigurablePrinter getConfiguration();

}