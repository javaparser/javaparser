package com.github.javaparser.printer.configuration;

import java.util.Optional;
import java.util.Set;

import com.github.javaparser.printer.configuration.PrinterConfiguration.ConfigOption;

/*
 * This interface defines the api for printer configuration
 */
public interface ConfigurablePrinter {

    /*
     * add or update an option
     */
    ConfigurablePrinter addOption(ConfigOption option);
    
    /*
     * Remove an option
     */
    ConfigurablePrinter removeOption(ConfigOption option);

    /*
     * True if an option is activated
     */
    boolean isActivated(ConfigOption option);

    /*
     * returns the specified option
     */
    Optional<ConfigOption> get(ConfigOption option);

    /*
     * returns all activated options
     */
    Set<ConfigOption> get();

    /*
     * returns the indentation parameters
     */
    Indentation getIndentation();

    ConfigurablePrinter setIndentation(Indentation indentation);

}