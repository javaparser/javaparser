/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
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

import static com.github.javaparser.utils.Utils.assertNonNegative;
import static com.github.javaparser.utils.Utils.assertNotNull;
import static com.github.javaparser.utils.Utils.assertPositive;

import java.util.Optional;
import java.util.Set;

import com.github.javaparser.printer.PrettyPrinter;
import com.github.javaparser.printer.configuration.Indentation.IndentType;
import com.github.javaparser.printer.configuration.PrinterConfiguration.ConfigOption;

/**
 * Configuration options for the {@link PrettyPrinter}.
 * This class is no longer acceptable to use because it is not sufficiently configurable and it is too tied to a specific implementation
 * <p> Use {@link ConfigurablePrinter interface or PrinterConfiguration default implementation } instead.
 */
@Deprecated
public class PrettyPrinterConfiguration implements ConfigurablePrinter {
    
    
    ConfigurablePrinter wrapped;
    
    /**
     * Indent the case when it is true, don't if false
     * switch(x) {            switch(x) {
     *    case 1:             case 1:
     *        return y;           return y;
     *    case 2:             case 2:
     *        return z;           return x;
     *}                       }
     */
    private Indentation indentation;
    
    /*
     * Default constructor
     */
    public PrettyPrinterConfiguration() {
        this.wrapped = new PrinterConfiguration();
        this.indentation = new Indentation(IndentType.SPACES, 4);
    }
    
    /*
     * returns the indentation parameters
     */
    public Indentation getIndentation() {
        return indentation;
    }
    
    public PrettyPrinterConfiguration setIndentation(Indentation indentation) {
        this.indentation = indentation;
        return this;
    }

    /**
     * @return the string that will be used to indent.
     * @deprecated (@see Indentation.getIndent())
     */
    @Deprecated
    public String getIndent() {
        return indentation.getIndent();
    }

    /**
     * @return the indentation size.
     * @deprecated (@see Indentation.size)
     */
    @Deprecated
    public int getIndentSize() {
        return indentation.getSize();
    }

    /**
     * Set the size of the indent in characters.
     * @deprecated (@see Indentation.size())
     */
    @Deprecated
    public PrettyPrinterConfiguration setIndentSize(int indentSize) {
        this.indentation.setSize(assertNonNegative(indentSize));
        return this;
    }

    /**
     * Get the type of indent to produce.
     * @deprecated (@see Indentation.type)
     */
    @Deprecated
    public IndentType getIndentType() {
        return this.indentation.getType();
    }

    /**
     * Set the type of indent to produce.
     * @deprecated (@see Indentation.type())
     */
    @Deprecated
    public PrettyPrinterConfiguration setIndentType(IndentType indentType) {
        this.indentation.setType(assertNotNull(indentType));
        return this;
    }



    /**
     * Get the tab width for pretty aligning.
     * @deprecated (@see Indentation.size)
     */
    @Deprecated
    public int getTabWidth() {
        return this.indentation.getSize();
    }

    /**
     * Set the tab width for pretty aligning.
     * @deprecated (@see Indentation.size)
     */
    @Deprecated
    public PrettyPrinterConfiguration setTabWidth(int tabWidth) {
        this.indentation.setSize(assertPositive(tabWidth));
        return this;
    }

    public boolean isOrderImports() {
        return get(ConfigOption.ORDER_IMPORTS).isPresent();
    }

    public boolean isPrintComments() {
        return get(ConfigOption.PRINT_COMMENTS).isPresent();
    }

    public boolean isIgnoreComments() {
        return !get(ConfigOption.PRINT_COMMENTS).isPresent();
    }
    
    public boolean isSpaceAroundOperators() {
        return get(ConfigOption.SPACE_AROUND_OPERATORS).isPresent();
    }

    public boolean isPrintJavadoc() {
        return get(ConfigOption.PRINT_JAVADOC).isPresent();
    }

    public boolean isColumnAlignParameters() {
        return get(ConfigOption.COLUMN_ALIGN_PARAMETERS).isPresent();
    }

    public boolean isColumnAlignFirstMethodChain() {
        return get(ConfigOption.COLUMN_ALIGN_FIRST_METHOD_CHAIN).isPresent();
    }

    public boolean isIndentCaseInSwitch() {
        return get(ConfigOption.INDENT_CASE_IN_SWITCH).isPresent();
    }


    /**
     * When true, all comments will be printed, unless printJavadoc is false, then only line and block comments will be
     * printed.
     */
    public PrettyPrinterConfiguration setPrintComments(boolean printComments) {
        wrapped = printComments ? addOption(ConfigOption.PRINT_COMMENTS) : removeOption(ConfigOption.PRINT_COMMENTS);
        return this;
    }

    /**
     * When true, Javadoc will be printed.
     */
    public PrettyPrinterConfiguration setPrintJavadoc(boolean printJavadoc) {
        wrapped = printJavadoc ? addOption(ConfigOption.PRINT_JAVADOC) : removeOption(ConfigOption.PRINT_JAVADOC);
        return this;
    }

    /**
     * Set if there should be spaces between operators
     */
    public PrettyPrinterConfiguration setSpaceAroundOperators(boolean spaceAroundOperators){
        wrapped = spaceAroundOperators ? addOption(ConfigOption.SPACE_AROUND_OPERATORS) : removeOption(ConfigOption.SPACE_AROUND_OPERATORS);
        return this;
    }

    public PrettyPrinterConfiguration setColumnAlignParameters(boolean columnAlignParameters) {
        wrapped = columnAlignParameters ? addOption(ConfigOption.COLUMN_ALIGN_PARAMETERS) : removeOption(ConfigOption.COLUMN_ALIGN_PARAMETERS);
        return this;
    }

    public PrettyPrinterConfiguration setColumnAlignFirstMethodChain(boolean columnAlignFirstMethodChain) {
        wrapped = columnAlignFirstMethodChain ? addOption(ConfigOption.COLUMN_ALIGN_FIRST_METHOD_CHAIN) : removeOption(ConfigOption.COLUMN_ALIGN_FIRST_METHOD_CHAIN);
        return this;
    }

    public PrettyPrinterConfiguration setIndentCaseInSwitch(boolean indentInSwitch) {
        wrapped = indentInSwitch ? addOption(ConfigOption.INDENT_CASE_IN_SWITCH) : removeOption(ConfigOption.INDENT_CASE_IN_SWITCH);
        return this;
    }

    public String getEndOfLineCharacter() {
        return get(ConfigOption.END_OF_LINE_CHARACTER).get().asValue();
    }

    /**
     * Set the character to append when a line should end. Example values: "\n", "\r\n", "".
     */
    public PrettyPrinterConfiguration setEndOfLineCharacter(String endOfLineCharacter) {
        addOption(ConfigOption.END_OF_LINE_CHARACTER.value(endOfLineCharacter));
        return this;
    }

    /**
     * When true, orders imports by alphabetically.
     */
    public PrettyPrinterConfiguration setOrderImports(boolean orderImports) {
        wrapped = orderImports ? addOption(ConfigOption.ORDER_IMPORTS) : removeOption(ConfigOption.ORDER_IMPORTS);
        return this;
    }



    public int getMaxEnumConstantsToAlignHorizontally() {
        return get(ConfigOption.DEFAULT_MAX_ENUM_CONSTANTS_TO_ALIGN_HORIZONTALLY).get().asInteger();
    }

    /**
     * By default enum constants get aligned like this:
     * <pre>
     *     enum X {
     *        A, B, C, D
     *     }
     * </pre>
     * until the amount of constants passes this value (5 by default).
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
        addOption(ConfigOption.DEFAULT_MAX_ENUM_CONSTANTS_TO_ALIGN_HORIZONTALLY.value(maxEnumConstantsToAlignHorizontally));
        return this;
    }

    @Override
    public ConfigurablePrinter addOption(ConfigOption option) {
        return wrapped.addOption(option);
    }

    @Override
    public boolean isActivated(ConfigOption option) {
        return wrapped.isActivated(option);
    }

    @Override
    public Optional<ConfigOption> get(ConfigOption option) {
        return wrapped.get(option);
    }

    @Override
    public Set<ConfigOption> get() {
        return wrapped.get();
    }

    @Override
    public ConfigurablePrinter removeOption(ConfigOption option) {
        return wrapped.removeOption(option);
    }
}
