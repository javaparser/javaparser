package com.github.javaparser.printer;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.junit.jupiter.api.Test;

import com.github.javaparser.printer.configuration.PrinterConfiguration;
import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration;
import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration.ConfigOption;
import com.github.javaparser.utils.Utils;

class PrinterConfigurationTest {

    @Test
    void testDefaultConfigurationAndValue() {
        PrinterConfiguration config = new DefaultPrinterConfiguration();
        assertTrue(config.get(ConfigOption.PRINT_COMMENTS).isPresent());
        assertTrue(config.get(ConfigOption.PRINT_JAVADOC).isPresent());
        assertTrue(config.get(ConfigOption.SPACE_AROUND_OPERATORS).isPresent());
        assertTrue(config.get(ConfigOption.INDENT_CASE_IN_SWITCH).isPresent());
        assertTrue(config.get(ConfigOption.MAX_ENUM_CONSTANTS_TO_ALIGN_HORIZONTALLY).isPresent());
        assertTrue(config.get(ConfigOption.END_OF_LINE_CHARACTER).isPresent());
        // values
        assertEquals(config.get(ConfigOption.MAX_ENUM_CONSTANTS_TO_ALIGN_HORIZONTALLY).get().asValue(),
                Integer.valueOf(5));
        assertEquals(config.get(ConfigOption.MAX_ENUM_CONSTANTS_TO_ALIGN_HORIZONTALLY).get().asValue(),
                Integer.valueOf(5));
        assertTrue(config.get(ConfigOption.MAX_ENUM_CONSTANTS_TO_ALIGN_HORIZONTALLY).get().asValue() ==
                Integer.valueOf(5));
        assertEquals(config.get(ConfigOption.END_OF_LINE_CHARACTER).get().asString(), Utils.SYSTEM_EOL);
    }

    @Test
    void testConfigurationError() {
        PrinterConfiguration config = new DefaultPrinterConfiguration();
        // verify configuration error case
        assertThrows(IllegalArgumentException.class, () -> {
            config.get(ConfigOption.PRINT_COMMENTS).get().asValue();
        });
        
        // verify value assignment: example we cannot assign a string to a boolean
        assertThrows(IllegalArgumentException.class, () -> {
            config.addOption(ConfigOption.PRINT_COMMENTS.value("1"));
        });
    }
    
    @Test
    void testUpdatedConfigurationOption() {
        PrinterConfiguration config = new DefaultPrinterConfiguration();
        // change the default value of the MAX_ENUM_CONSTANTS_TO_ALIGN_HORIZONTALLY option
        config.get(ConfigOption.MAX_ENUM_CONSTANTS_TO_ALIGN_HORIZONTALLY).get().value(2);
        // verify the value is updated
        assertEquals(config.get(ConfigOption.MAX_ENUM_CONSTANTS_TO_ALIGN_HORIZONTALLY).get().asValue(), Integer.valueOf(2));
    }
    
    @Test
    void testRemoveOption() {
        PrinterConfiguration config = new DefaultPrinterConfiguration();
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
