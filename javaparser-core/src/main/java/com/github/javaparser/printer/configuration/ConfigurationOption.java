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

public interface ConfigurationOption {

    /* 
    * Set a currentValue to an option
    */
    ConfigurationOption value(Object value);

    /*
     * returns True if the option has a currentValue
     */
    boolean hasValue();

    /*
     * returns the currentValue as an Integer
     */
    Integer asInteger();

    /*
     * returns the currentValue as a String
     */
    String asString();

    /*
     * returns the currentValue as a Boolean
     */
    Boolean asBoolean();

    <T extends Object> T asValue();
}
