package com.github.javaparser.printer;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.junit.jupiter.api.Test;

import com.github.javaparser.printer.configuration.ConfigurablePrinter;
import com.github.javaparser.printer.configuration.PrinterConfiguration;
import com.github.javaparser.printer.configuration.PrinterConfiguration.ConfigOption;
import com.github.javaparser.utils.Utils;

class PrinterConfigurationTest {

    @Test
    void testDefaultConfigurationAndValue() {
        ConfigurablePrinter config = new PrinterConfiguration();
        assertTrue(config.get(ConfigOption.PRINT_COMMENTS).isPresent());
        assertTrue(config.get(ConfigOption.PRINT_JAVADOC).isPresent());
        assertTrue(config.get(ConfigOption.SPACE_AROUND_OPERATORS).isPresent());
        assertTrue(config.get(ConfigOption.INDENT_CASE_IN_SWITCH).isPresent());
        assertTrue(config.get(ConfigOption.DEFAULT_MAX_ENUM_CONSTANTS_TO_ALIGN_HORIZONTALLY).isPresent());
        assertTrue(config.get(ConfigOption.END_OF_LINE_CHARACTER).isPresent());
        // values
        assertEquals(config.get(ConfigOption.DEFAULT_MAX_ENUM_CONSTANTS_TO_ALIGN_HORIZONTALLY).get().asValue(),
                Integer.valueOf(5));
        assertEquals(config.get(ConfigOption.DEFAULT_MAX_ENUM_CONSTANTS_TO_ALIGN_HORIZONTALLY).get().asValue(),
                Integer.valueOf(5));
        assertTrue(config.get(ConfigOption.DEFAULT_MAX_ENUM_CONSTANTS_TO_ALIGN_HORIZONTALLY).get().asValue() ==
                Integer.valueOf(5));
        assertEquals(config.get(ConfigOption.END_OF_LINE_CHARACTER).get().asString(), Utils.SYSTEM_EOL);
    }

    @Test
    void testConfigurationError() {
        ConfigurablePrinter config = new PrinterConfiguration();
        // verify configuration error case
        assertThrows(IllegalArgumentException.class, () -> {
            config.get(ConfigOption.PRINT_COMMENTS).get().asValue();
        });
    }
    
    @Test
    void testUpdatedConfigurationOption() {
        ConfigurablePrinter config = new PrinterConfiguration();
        // change the default value of the DEFAULT_MAX_ENUM_CONSTANTS_TO_ALIGN_HORIZONTALLY option
        config.get(ConfigOption.DEFAULT_MAX_ENUM_CONSTANTS_TO_ALIGN_HORIZONTALLY).get().value(2);
        // verify the value is updated
        assertEquals(config.get(ConfigOption.DEFAULT_MAX_ENUM_CONSTANTS_TO_ALIGN_HORIZONTALLY).get().asValue(), Integer.valueOf(2));
    }
    
    @Test
    void testRemoveOption() {
        ConfigurablePrinter config = new PrinterConfiguration();
        assertTrue(config.get(ConfigOption.PRINT_COMMENTS).isPresent());
        assertTrue(config.get(ConfigOption.END_OF_LINE_CHARACTER).isPresent());
        // remove option PRINT_COMMENTS
        config.removeOption(ConfigOption.PRINT_COMMENTS);
        assertFalse(config.get(ConfigOption.PRINT_COMMENTS).isPresent());
        // remove option with value
        config.removeOption(ConfigOption.END_OF_LINE_CHARACTER.value("\n"));
        assertFalse(config.get(ConfigOption.END_OF_LINE_CHARACTER).isPresent());
    }

}
