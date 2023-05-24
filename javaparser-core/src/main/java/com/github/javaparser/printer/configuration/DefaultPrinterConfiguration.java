/*
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

import com.github.javaparser.printer.Printer;
import com.github.javaparser.printer.configuration.Indentation.IndentType;
import com.github.javaparser.utils.Utils;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Optional;
import java.util.Set;

/**
 * Configuration options for the {@link Printer}.
 */
public class DefaultPrinterConfiguration implements PrinterConfiguration {

    public enum ConfigOption {

        /**
         * Order imports alphabetically
         */
        ORDER_IMPORTS(Boolean.class),
        /**
         * The logic to be used when ordering the imports.
         */
        SORT_IMPORTS_STRATEGY(ImportOrderingStrategy.class),
        /**
         * Print comments only. It can be combined with {@code PRINT_JAVADOC} to print regular comments and javadoc.
         */
        PRINT_COMMENTS(Boolean.class),
        /**
         * Print javadoc comments only. It can be combined with {@code PRINT_COMMENTS} to print regular javadoc and comments
         */
        PRINT_JAVADOC(Boolean.class),
        SPACE_AROUND_OPERATORS(Boolean.class),
        COLUMN_ALIGN_PARAMETERS(Boolean.class),
        COLUMN_ALIGN_FIRST_METHOD_CHAIN(Boolean.class),
        /**
         * Indent the case when it is true, don't if false
         * <pre>{@code
         * switch(x) {            switch(x) {
         *    case 1:             case 1:
         *        return y;           return y;
         *    case 2:             case 2:
         *        return z;           return x;
         * }                       }
         * }<pre>
         */
        INDENT_CASE_IN_SWITCH(Boolean.class),
        /**
         * By default enum constants get aligned like this:
         * <pre>{@code
         *     enum X {
         *        A, B, C, D
         *     }
         * }<pre>
         * until the amount of constants passes this currentValue (5 by default).
         * Then they get aligned like this:
         * <pre>{@code
         *     enum X {
         *        A,
         *        B,
         *        C,
         *        D,
         *        E,
         *        F,
         *        G
         *     }
         * }</pre>
         * Set it to a very large number (e.g. {@code Integer.MAX_VALUE} to always align horizontally.
         * Set it to 1 or less to always align vertically.
         */
        MAX_ENUM_CONSTANTS_TO_ALIGN_HORIZONTALLY(Integer.class, Integer.valueOf(5)),
        END_OF_LINE_CHARACTER(String.class, Utils.SYSTEM_EOL),
        /**
         * Indentation proprerty
         */
        INDENTATION(Indentation.class, new Indentation(IndentType.SPACES, 4));

        Object defaultValue;

        Class type;

        // DefaultConfigurationOption without currentValue
        ConfigOption(Class clazz) {
            this.type = clazz;
        }

        // DefaultConfigurationOption with initial currentValue
        ConfigOption(Class clazz, Object value) {
            this.type = clazz;
            if (!(this.type.isAssignableFrom(value.getClass()))) {
                throw new IllegalArgumentException(String.format("%s is not an instance of %s", value, type.getName()));
            }
            this.defaultValue = value;
        }
    }

    // contains all available options
    // an option contained in the set is considered as activated
    private Set<ConfigurationOption> defaultOptions = new HashSet<>(Arrays.asList(new DefaultConfigurationOption(ConfigOption.PRINT_COMMENTS, ConfigOption.PRINT_COMMENTS.defaultValue), new DefaultConfigurationOption(ConfigOption.PRINT_JAVADOC, ConfigOption.PRINT_JAVADOC.defaultValue), new DefaultConfigurationOption(ConfigOption.SPACE_AROUND_OPERATORS, ConfigOption.SPACE_AROUND_OPERATORS.defaultValue), new DefaultConfigurationOption(ConfigOption.INDENT_CASE_IN_SWITCH, ConfigOption.INDENT_CASE_IN_SWITCH.defaultValue), new DefaultConfigurationOption(ConfigOption.MAX_ENUM_CONSTANTS_TO_ALIGN_HORIZONTALLY, ConfigOption.MAX_ENUM_CONSTANTS_TO_ALIGN_HORIZONTALLY.defaultValue), new DefaultConfigurationOption(ConfigOption.END_OF_LINE_CHARACTER, ConfigOption.END_OF_LINE_CHARACTER.defaultValue), new DefaultConfigurationOption(ConfigOption.INDENTATION, ConfigOption.INDENTATION.defaultValue)));

    public DefaultPrinterConfiguration() {
    }

    /*
     * add the specified option if it does not exist or replace the existing option
     */
    @Override
    public PrinterConfiguration addOption(ConfigurationOption option) {
        removeOption(option);
        defaultOptions.add(option);
        return this;
    }

    /*
     * remove the specified option
     */
    @Override
    public PrinterConfiguration removeOption(ConfigurationOption option) {
        defaultOptions.remove(option);
        return this;
    }

    /*
     * True if an option is activated
     */
    @Override
    public boolean isActivated(ConfigurationOption option) {
        return defaultOptions.contains(option);
    }

    /*
     * returns the specified option
     */
    @Override
    public Optional<ConfigurationOption> get(ConfigurationOption option) {
        return defaultOptions.stream().filter(o -> o.equals(option)).findFirst();
    }

    /**
     * returns all options configured
     */
    @Override
    public Set<ConfigurationOption> get() {
        return defaultOptions;
    }
}
