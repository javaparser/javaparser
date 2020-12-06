/*
 * Copyright (C) 2011, 2013-2020 The JavaParser Team.
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

import java.util.Arrays;
import java.util.HashSet;
import java.util.Optional;
import java.util.Set;

import com.github.javaparser.printer.Printable;
import com.github.javaparser.printer.configuration.Indentation.IndentType;
import com.github.javaparser.utils.Utils;

/**
 * Configuration options for the {@link Printable}.
 */
public class PrinterConfiguration implements ConfigurablePrinter {
    
    public enum ConfigOption {
        /**
         * Order imports alphabetically
         */
        ORDER_IMPORTS(Boolean.class), 
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
         * until the amount of constants passes this value (5 by default).
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
        DEFAULT_MAX_ENUM_CONSTANTS_TO_ALIGN_HORIZONTALLY(Integer.valueOf(5)),
        END_OF_LINE_CHARACTER(Utils.SYSTEM_EOL);
        
        Object value;
        
        Class type;
        
        // Option without value
        <T> ConfigOption(Class clazz) {
            this.type = clazz;
        }
        
        // Option with initial value
        ConfigOption(Object value) {
            value(value);
        }
        
       /* 
        * Set a value to an option
        */
        public ConfigOption value(Object value) {
            Utils.assertNotNull(value);
            this.value = value;
            this.type = value.getClass();
            return this;
        }
        
        /*
         * returns True if the option has a value
         */
        public boolean hasValue() {
            return value != null;
        }
        
        /*
         * returns the value as an Integer
         */
        public Integer asInteger() {
            return cast(); 
        }
        
        /*
         * returns the value as a String
         */
        public String asString() {
            return cast(); 
        }
        
        /*
         * returns the value as a Boolean
         */
        public Boolean asBoolean() {
            return cast(); 
        }
        
        public <T extends Object> T asValue() {
            return cast(); 
        }
        
        private <T extends Object> T cast() {
            if (!hasValue()) throw new IllegalArgumentException(String.format("The option %s has no value", this.name()));
            if (type.isAssignableFrom(value.getClass()))
                return (T) type.cast(value);
            throw new IllegalArgumentException(String.format("%s cannot be cast to %s", value, type.getName()));
        }
    }

    // contains all available options
    // an option contained in the set is considered as activated
    private Set<ConfigOption> options = new HashSet<ConfigOption>(Arrays.asList(
            ConfigOption.PRINT_COMMENTS, 
            ConfigOption.PRINT_JAVADOC, 
            ConfigOption.SPACE_AROUND_OPERATORS,
            ConfigOption.INDENT_CASE_IN_SWITCH,
            ConfigOption.DEFAULT_MAX_ENUM_CONSTANTS_TO_ALIGN_HORIZONTALLY.value(Integer.valueOf(5)),
            ConfigOption.END_OF_LINE_CHARACTER.value(Utils.SYSTEM_EOL)
            ));

    private Indentation indentation = new Indentation(IndentType.SPACES, 4);
    
    /*
     * add the specified option if it does not exist or replace the existing option
     */
    @Override
    public ConfigurablePrinter addOption(ConfigOption option) {
        removeOption(option);
        options.add(option);
        return this;
    }
    
    /*
     * remove the specified option
     */
    @Override
    public ConfigurablePrinter removeOption(ConfigOption option) {
        options.remove(option);
        return this;
    }
    
    /*
     * True if an option is activated
     */
    @Override
    public boolean isActivated(ConfigOption option) {
        return options.contains(option);
    }
    
    /*
     * returns the specified option
     */
    @Override
    public Optional<ConfigOption> get(ConfigOption option) {
        return options.stream().filter(o-> o.equals(option)).findFirst();
    }
    
    /*
     * returns all activated options
     */
    @Override
    public Set<ConfigOption> get() {
        return options;
    }
    
    /*
     * returns the indentation parameters
     */
    @Override
    public Indentation getIndentation() {
        return indentation;
    }
    
    @Override
    public ConfigurablePrinter setIndentation(Indentation indentation) {
        this.indentation = indentation;
        return this;
    }

}
