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