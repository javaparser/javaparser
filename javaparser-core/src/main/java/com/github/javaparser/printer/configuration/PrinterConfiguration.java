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
    PrinterConfiguration addOption(ConfigurationOption option);

    /*
     * Remove an option
     */
    PrinterConfiguration removeOption(ConfigurationOption option);

    /*
     * True if an option is activated
     */
    boolean isActivated(ConfigurationOption option);

    /*
     * returns the specified option
     */
    Optional<ConfigurationOption> get(ConfigurationOption option);

    /*
     * returns all activated options
     */
    Set<ConfigurationOption> get();

}
