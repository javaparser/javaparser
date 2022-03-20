package com.github.javaparser.printer;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.Optional;

import org.junit.jupiter.api.Test;

import com.github.javaparser.printer.configuration.ConfigurationOption;
import com.github.javaparser.printer.configuration.DefaultConfigurationOption;
import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration;
import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration.ConfigOption;
import com.github.javaparser.printer.configuration.PrinterConfiguration;
import com.github.javaparser.utils.Utils;

class PrinterConfigurationTest {
    
    private Optional<ConfigurationOption> getOption(PrinterConfiguration config, ConfigOption cOption) {
        return config.get(new DefaultConfigurationOption(cOption));
    }

    @Test
    void testDefaultConfigurationAndValue() {
        PrinterConfiguration config = new DefaultPrinterConfiguration();
        assertTrue(getOption(config, ConfigOption.PRINT_COMMENTS).isPresent());
        assertTrue(getOption(config, ConfigOption.PRINT_JAVADOC).isPresent());
        assertTrue(getOption(config, ConfigOption.SPACE_AROUND_OPERATORS).isPresent());
        assertTrue(getOption(config, ConfigOption.INDENT_CASE_IN_SWITCH).isPresent());
        assertTrue(getOption(config, ConfigOption.MAX_ENUM_CONSTANTS_TO_ALIGN_HORIZONTALLY).isPresent());
        assertTrue(getOption(config, ConfigOption.END_OF_LINE_CHARACTER).isPresent());
        // values
        assertEquals(getOption(config, ConfigOption.MAX_ENUM_CONSTANTS_TO_ALIGN_HORIZONTALLY).get().asValue(),
                Integer.valueOf(5));
        assertEquals(getOption(config, ConfigOption.MAX_ENUM_CONSTANTS_TO_ALIGN_HORIZONTALLY).get().asValue(),
                Integer.valueOf(5));
        assertTrue(getOption(config, ConfigOption.MAX_ENUM_CONSTANTS_TO_ALIGN_HORIZONTALLY).get().asValue() ==
                Integer.valueOf(5));
        assertEquals(getOption(config, ConfigOption.END_OF_LINE_CHARACTER).get().asString(), Utils.SYSTEM_EOL);
    }

    @Test
    void testConfigurationError() {
        PrinterConfiguration config = new DefaultPrinterConfiguration();
        // verify configuration error case
        assertThrows(IllegalArgumentException.class, () -> {
            getOption(config, ConfigOption.PRINT_COMMENTS).get().asValue();
        });
        
        // verify currentValue assignment: example we cannot assign a string to a boolean
        assertThrows(IllegalArgumentException.class, () -> {
            config.addOption(new DefaultConfigurationOption(ConfigOption.PRINT_COMMENTS, "1"));
        });
    }
    
    @Test
    void testUpdatedConfigurationOption() {
        PrinterConfiguration config = new DefaultPrinterConfiguration();
        // change the default currentValue of the MAX_ENUM_CONSTANTS_TO_ALIGN_HORIZONTALLY option
        getOption(config, ConfigOption.MAX_ENUM_CONSTANTS_TO_ALIGN_HORIZONTALLY).get().value(2);
        // verify the currentValue is updated
        assertEquals(getOption(config, ConfigOption.MAX_ENUM_CONSTANTS_TO_ALIGN_HORIZONTALLY).get().asValue(), Integer.valueOf(2));
    }
    
    @Test
    void testRemoveOption() {
        PrinterConfiguration config = new DefaultPrinterConfiguration();
        assertTrue(getOption(config, ConfigOption.PRINT_COMMENTS).isPresent());
        assertTrue(getOption(config, ConfigOption.END_OF_LINE_CHARACTER).isPresent());
        // remove option PRINT_COMMENTS
        config.removeOption(new DefaultConfigurationOption(ConfigOption.PRINT_COMMENTS));
        assertFalse(getOption(config, ConfigOption.PRINT_COMMENTS).isPresent());
        // remove option with currentValue
        config.removeOption(new DefaultConfigurationOption(ConfigOption.END_OF_LINE_CHARACTER, "\n"));
        assertFalse(getOption(config, ConfigOption.END_OF_LINE_CHARACTER).isPresent());
    }

}
