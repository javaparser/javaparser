package com.github.javaparser.printer.configuration;

import java.util.Optional;
import java.util.Set;

/**
 * This interface defines the API for printer configuration.
 * An option can be added or removed from the configuration. An indentation can also be added to it.
 */
public interface PrinterConfiguration {

    /*
     * add or update an option
     */
    PrinterConfiguration addOption(ConfigurableOption option);
    
    /*
     * Remove an option
     */
    PrinterConfiguration removeOption(ConfigurableOption option);

    /*
     * True if an option is activated
     */
    boolean isActivated(ConfigurableOption option);

    /*
     * returns the specified option
     */
    Optional<ConfigurableOption> get(ConfigurableOption option);

    /*
     * returns all activated options
     */
    Set<ConfigurableOption> get();

}