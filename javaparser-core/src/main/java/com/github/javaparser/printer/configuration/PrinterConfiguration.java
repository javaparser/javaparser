/*
 * Copyright (C) 2013-2023 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */
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
