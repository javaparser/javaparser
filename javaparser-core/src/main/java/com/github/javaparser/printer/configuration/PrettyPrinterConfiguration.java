/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
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

import com.github.javaparser.printer.PrettyPrinter;
import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration.ConfigOption;
import com.github.javaparser.printer.configuration.Indentation.IndentType;
import java.util.Optional;
import java.util.Set;
import static com.github.javaparser.utils.Utils.*;

/**
 * Configuration options for the {@link PrettyPrinter}.
 * This class is no longer acceptable to use because it is not sufficiently configurable and it is too tied to a specific implementation
 * <p> Use {@link PrinterConfiguration interface or DefaultPrinterConfiguration default implementation } instead.
 * @deprecated This class could be removed in a future version. Use default DefaultPrinterConfiguration.
 */
@Deprecated
public class PrettyPrinterConfiguration implements PrinterConfiguration {

    PrinterConfiguration wrappedConfiguration;

    /*
     * Default constructor
     */
    public PrettyPrinterConfiguration() {
        this.wrappedConfiguration = new DefaultPrinterConfiguration();
    }

    /*
     * returns the indentation parameters
     */
    public Indentation getIndentation() {
        return wrappedConfiguration.get(new DefaultConfigurationOption(ConfigOption.INDENTATION)).get().asValue();
    }

    public PrettyPrinterConfiguration setIndentation(Indentation indentation) {
        wrappedConfiguration.addOption(new DefaultConfigurationOption(ConfigOption.INDENTATION, indentation));
        return this;
    }

    /**
     * @return the string that will be used to indent.
     * @deprecated (@see Indentation.getIndent())
     */
    @Deprecated
    public String getIndent() {
        return getIndentation().getIndent();
    }

    /**
     * @return the indentation size.
     * @deprecated (@see Indentation.size)
     */
    @Deprecated
    public int getIndentSize() {
        return getIndentation().getSize();
    }

    /**
     * Set the size of the indent in characters.
     * @deprecated (@see Indentation.size())
     */
    @Deprecated
    public PrettyPrinterConfiguration setIndentSize(int indentSize) {
        Indentation indentation = getIndentation().setSize(assertNonNegative(indentSize));
        setIndentation(indentation);
        return this;
    }

    /**
     * Get the type of indent to produce.
     * @deprecated (@see Indentation.type)
     */
    @Deprecated
    public IndentType getIndentType() {
        return getIndentation().getType();
    }

    /**
     * Set the type of indent to produce.
     * @deprecated (@see Indentation.type())
     */
    @Deprecated
    public PrettyPrinterConfiguration setIndentType(IndentType indentType) {
        Indentation indentation = getIndentation().setType(assertNotNull(indentType));
        setIndentation(indentation);
        return this;
    }

    /**
     * Get the tab width for pretty aligning.
     * @deprecated (@see Indentation.size)
     */
    @Deprecated
    public int getTabWidth() {
        return getIndentation().getSize();
    }

    /**
     * Set the tab width for pretty aligning.
     * @deprecated (@see Indentation.size)
     */
    @Deprecated
    public PrettyPrinterConfiguration setTabWidth(int tabWidth) {
        setIndentSize(assertPositive(tabWidth));
        return this;
    }

    public boolean isOrderImports() {
        return wrappedConfiguration.get(new DefaultConfigurationOption(ConfigOption.ORDER_IMPORTS)).isPresent();
    }

    public boolean isPrintComments() {
        return wrappedConfiguration.get(new DefaultConfigurationOption(ConfigOption.PRINT_COMMENTS)).isPresent();
    }

    public boolean isIgnoreComments() {
        return !wrappedConfiguration.get(new DefaultConfigurationOption(ConfigOption.PRINT_COMMENTS)).isPresent();
    }

    public boolean isSpaceAroundOperators() {
        return wrappedConfiguration.get(new DefaultConfigurationOption(ConfigOption.SPACE_AROUND_OPERATORS)).isPresent();
    }

    public boolean isPrintJavadoc() {
        return wrappedConfiguration.get(new DefaultConfigurationOption(ConfigOption.PRINT_JAVADOC)).isPresent();
    }

    public boolean isColumnAlignParameters() {
        return wrappedConfiguration.get(new DefaultConfigurationOption(ConfigOption.COLUMN_ALIGN_PARAMETERS)).isPresent();
    }

    public boolean isColumnAlignFirstMethodChain() {
        return wrappedConfiguration.get(new DefaultConfigurationOption(ConfigOption.COLUMN_ALIGN_FIRST_METHOD_CHAIN)).isPresent();
    }

    public boolean isIndentCaseInSwitch() {
        return wrappedConfiguration.get(new DefaultConfigurationOption(ConfigOption.INDENT_CASE_IN_SWITCH)).isPresent();
    }

    /**
     * When true, all comments will be printed, unless printJavadoc is false, then only line and block comments will be
     * printed.
     */
    public PrettyPrinterConfiguration setPrintComments(boolean printComments) {
        wrappedConfiguration = printComments ? addOption(new DefaultConfigurationOption(ConfigOption.PRINT_COMMENTS)) : removeOption(new DefaultConfigurationOption(ConfigOption.PRINT_COMMENTS));
        return this;
    }

    /**
     * When true, Javadoc will be printed.
     */
    public PrettyPrinterConfiguration setPrintJavadoc(boolean printJavadoc) {
        wrappedConfiguration = printJavadoc ? addOption(new DefaultConfigurationOption(ConfigOption.PRINT_JAVADOC)) : removeOption(new DefaultConfigurationOption(ConfigOption.PRINT_JAVADOC));
        return this;
    }

    /**
     * Set if there should be spaces between operators
     */
    public PrettyPrinterConfiguration setSpaceAroundOperators(boolean spaceAroundOperators) {
        wrappedConfiguration = spaceAroundOperators ? addOption(new DefaultConfigurationOption(ConfigOption.SPACE_AROUND_OPERATORS)) : removeOption(new DefaultConfigurationOption(ConfigOption.SPACE_AROUND_OPERATORS));
        return this;
    }

    public PrettyPrinterConfiguration setColumnAlignParameters(boolean columnAlignParameters) {
        wrappedConfiguration = columnAlignParameters ? addOption(new DefaultConfigurationOption(ConfigOption.COLUMN_ALIGN_PARAMETERS)) : removeOption(new DefaultConfigurationOption(ConfigOption.COLUMN_ALIGN_PARAMETERS));
        return this;
    }

    public PrettyPrinterConfiguration setColumnAlignFirstMethodChain(boolean columnAlignFirstMethodChain) {
        wrappedConfiguration = columnAlignFirstMethodChain ? addOption(new DefaultConfigurationOption(ConfigOption.COLUMN_ALIGN_FIRST_METHOD_CHAIN)) : removeOption(new DefaultConfigurationOption(ConfigOption.COLUMN_ALIGN_FIRST_METHOD_CHAIN));
        return this;
    }

    public PrettyPrinterConfiguration setIndentCaseInSwitch(boolean indentInSwitch) {
        wrappedConfiguration = indentInSwitch ? addOption(new DefaultConfigurationOption(ConfigOption.INDENT_CASE_IN_SWITCH)) : removeOption(new DefaultConfigurationOption(ConfigOption.INDENT_CASE_IN_SWITCH));
        return this;
    }

    public String getEndOfLineCharacter() {
        return wrappedConfiguration.get(new DefaultConfigurationOption(ConfigOption.END_OF_LINE_CHARACTER)).get().asValue();
    }

    /**
     * Set the character to append when a line should end. Example values: "\n", "\r\n", "".
     */
    public PrettyPrinterConfiguration setEndOfLineCharacter(String endOfLineCharacter) {
        addOption(new DefaultConfigurationOption(ConfigOption.END_OF_LINE_CHARACTER, endOfLineCharacter));
        return this;
    }

    /**
     * When true, orders imports by alphabetically.
     */
    public PrettyPrinterConfiguration setOrderImports(boolean orderImports) {
        wrappedConfiguration = orderImports ? addOption(new DefaultConfigurationOption(ConfigOption.ORDER_IMPORTS)) : removeOption(new DefaultConfigurationOption(ConfigOption.ORDER_IMPORTS));
        return this;
    }

    public int getMaxEnumConstantsToAlignHorizontally() {
        return wrappedConfiguration.get(new DefaultConfigurationOption(ConfigOption.MAX_ENUM_CONSTANTS_TO_ALIGN_HORIZONTALLY)).get().asInteger();
    }

    /**
     * By default enum constants get aligned like this:
     * <pre>
     *     enum X {
     *        A, B, C, D
     *     }
     * </pre>
     * until the amount of constants passes this currentValue (5 by default).
     * Then they get aligned like this:
     * <pre>
     *     enum X {
     *        A,
     *        B,
     *        C,
     *        D,
     *        E,
     *        F,
     *        G
     *     }
     * </pre>
     * Set it to a large number to always align horizontally.
     * Set it to 1 or less to always align vertically.
     */
    public PrettyPrinterConfiguration setMaxEnumConstantsToAlignHorizontally(int maxEnumConstantsToAlignHorizontally) {
        addOption(new DefaultConfigurationOption(ConfigOption.MAX_ENUM_CONSTANTS_TO_ALIGN_HORIZONTALLY, maxEnumConstantsToAlignHorizontally));
        return this;
    }

    @Override
    public PrinterConfiguration addOption(ConfigurationOption option) {
        return wrappedConfiguration.addOption(option);
    }

    @Override
    public boolean isActivated(ConfigurationOption option) {
        return wrappedConfiguration.isActivated(option);
    }

    @Override
    public Optional<ConfigurationOption> get(ConfigurationOption option) {
        return wrappedConfiguration.get(option);
    }

    @Override
    public Set<ConfigurationOption> get() {
        return wrappedConfiguration.get();
    }

    @Override
    public PrinterConfiguration removeOption(ConfigurationOption option) {
        return wrappedConfiguration.removeOption(option);
    }
}
