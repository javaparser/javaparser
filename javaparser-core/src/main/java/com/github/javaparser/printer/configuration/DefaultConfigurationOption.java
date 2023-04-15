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

import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration.ConfigOption;
import com.github.javaparser.utils.Utils;

/*
 * An option is a pair of ConfigOption and a currentValue
 */
public class DefaultConfigurationOption implements ConfigurationOption {

    ConfigOption configOption;

    Object currentValue;

    public DefaultConfigurationOption(ConfigOption configOption) {
        this(configOption, null);
    }

    public DefaultConfigurationOption(ConfigOption configOption, Object value) {
        this.configOption = configOption;
        if (value != null)
            value(value);
    }

    @Override
    public boolean equals(Object o) {
        if (o == null || !(o instanceof DefaultConfigurationOption))
            return false;
        DefaultConfigurationOption other = (DefaultConfigurationOption) o;
        return configOption.equals(other.configOption);
    }

    @Override
    public int hashCode() {
        return configOption.hashCode();
    }

    /**
     * Set a currentValue to an option
     */
    @Override
    public ConfigurationOption value(Object value) {
        Utils.assertNotNull(value);
        this.currentValue = value;
        // verify the currentValue's type
        if (!(configOption.type.isAssignableFrom(value.getClass()))) {
            throw new IllegalArgumentException(String.format("%s is not an instance of %s", value, configOption.type.getName()));
        }
        return this;
    }

    /**
     * returns True if the option has a currentValue
     */
    @Override
    public boolean hasValue() {
        return this.currentValue != null;
    }

    /**
     * returns the currentValue as an Integer
     */
    @Override
    public Integer asInteger() {
        return cast();
    }

    /**
     * returns the currentValue as a String
     */
    @Override
    public String asString() {
        return cast();
    }

    /**
     * returns the currentValue as a Boolean
     */
    @Override
    public Boolean asBoolean() {
        return cast();
    }

    @Override
    public <T extends Object> T asValue() {
        return cast();
    }

    private <T extends Object> T cast() {
        if (!hasValue())
            throw new IllegalArgumentException(String.format("The option %s has no currentValue", configOption.name()));
        if (configOption.type.isAssignableFrom(currentValue.getClass()))
            return (T) configOption.type.cast(currentValue);
        throw new IllegalArgumentException(String.format("%s cannot be cast to %s", currentValue, configOption.type.getName()));
    }
}
