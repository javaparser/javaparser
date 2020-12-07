package com.github.javaparser.printer.configuration;

import java.util.Optional;
import java.util.Set;

import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration.ConfigOption;

/**
 * This interface defines the API for printer configuration.
 * An option can be added or removed from the configuration. An indentation can also be added to it.
 */
public interface ConfigurationPrinter {

    /*
     * add or update an option
     */
    ConfigurationPrinter addOption(ConfigOption option);
    
    /*
     * Remove an option
     */
    ConfigurationPrinter removeOption(ConfigOption option);

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

    ConfigurationPrinter setIndentation(Indentation indentation);

}