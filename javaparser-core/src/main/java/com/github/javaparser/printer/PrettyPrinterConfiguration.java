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

package com.github.javaparser.printer;

import static com.github.javaparser.printer.PrettyPrinterConfiguration.IndentType.SPACES;
import static com.github.javaparser.utils.Utils.SYSTEM_EOL;
import static com.github.javaparser.utils.Utils.assertNonNegative;
import static com.github.javaparser.utils.Utils.assertNotNull;
import static com.github.javaparser.utils.Utils.assertPositive;

import java.util.function.Function;

import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * Configuration options for the {@link PrettyPrinter}.
 */
public class PrettyPrinterConfiguration {
    
    public static class Indentation {
        IndentType type;
        int size;
        public Indentation(IndentType type, int size) {
            this.type = type;
            this.size = size;
        }
        public Indentation size(int size) {
            this.size = size;
            return this;
        }
        public Indentation type(IndentType type) {
            this.type = type;
            return this;
        }
        public String getIndent() {
            StringBuilder indentString = new StringBuilder();
            char indentChar = type.getChar();
            for (int i = 0; i < size; i++) {
                indentString.append(indentChar);
            }
            return indentString.toString();
        }
    }
    
    public enum IndentType {
        /**
         * Indent with spaces.
         */
        SPACES(' '),

        /**
         * Indent with tabs as far as possible.
         * For proper aligning, the tab width is necessary and by default 4.
         */
        TABS('\t'),

        /**
         * Indent with tabs but align with spaces when wrapping and aligning
         * method call chains and method call parameters.
         *
         * <p/><i>Example result:</i>
         * <pre>
         * class Foo {
         *
         * \tvoid bar() {
         * \t\tfoo().bar()
         * \t\t......baz(() -*&gt; {
         * \t\t..........\tboo().baa()
         * \t\t..........\t......bee(a,
         * \t\t..........\t..........b,
         * \t\t..........\t..........c);
         * \t\t..........})
         * \t\t......bam();
         * \t}
         * }
         * </pre>
         */
        TABS_WITH_SPACE_ALIGN('\t');
        
        private Character car;
        
        private IndentType(Character c) {
            this.car = c;
        }
        
        public Character getChar() {
            return this.car;
        }
        
    }

    public static final int DEFAULT_MAX_ENUM_CONSTANTS_TO_ALIGN_HORIZONTALLY = 5;

    private boolean orderImports = false;
    private boolean printComments = true;
    private boolean printJavadoc = true;
    private boolean spaceAroundOperators = true;
    private boolean columnAlignParameters = false;
    private boolean columnAlignFirstMethodChain = false;
    /**
     * Indent the case when it is true, don't if false
     * switch(x) {            switch(x) {
     *    case 1:             case 1:
     *        return y;           return y;
     *    case 2:             case 2:
     *        return z;           return x;
     *}                       }
     */
    private boolean indentCaseInSwitch = true;
    private Indentation indentation = new Indentation(SPACES, 4);
//    private IndentType indentType = SPACES;
    private int tabWidth = 4;
//    private int indentSize = 4;
    private String endOfLineCharacter = SYSTEM_EOL;
    private Function<PrettyPrinterConfiguration, VoidVisitor<Void>> visitorFactory = PrettyPrintVisitor::new;
    private int maxEnumConstantsToAlignHorizontally = DEFAULT_MAX_ENUM_CONSTANTS_TO_ALIGN_HORIZONTALLY;
    
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
        return indentation.size;
    }

    /**
     * Set the size of the indent in characters.
     * @deprecated (@see Indentation.size())
     */
    @Deprecated
    public PrettyPrinterConfiguration setIndentSize(int indentSize) {
        this.indentation.size(assertNonNegative(indentSize));
        return this;
    }

    /**
     * Get the type of indent to produce.
     * @deprecated (@see Indentation.type)
     */
    public IndentType getIndentType() {
        return this.indentation.type;
    }

    /**
     * Set the type of indent to produce.
     * @deprecated (@see Indentation.type())
     */
    public PrettyPrinterConfiguration setIndentType(IndentType indentType) {
        this.indentation.type(assertNotNull(indentType));
        return this;
    }



    /**
     * Get the tab width for pretty aligning.
     */
    public int getTabWidth() {
        return tabWidth;
    }

    /**
     * Set the tab width for pretty aligning.
     */
    public PrettyPrinterConfiguration setTabWidth(int tabWidth) {
        this.tabWidth = assertPositive(tabWidth);
        return this;
    }

    public boolean isOrderImports() {
        return orderImports;
    }

    public boolean isPrintComments() {
        return printComments;
    }

    public boolean isIgnoreComments() {
        return !printComments;
    }
    
    public boolean isSpaceAroundOperators() { return spaceAroundOperators; }

    public boolean isPrintJavadoc() {
        return printJavadoc;
    }

    public boolean isColumnAlignParameters() {
        return columnAlignParameters;
    }

    public boolean isColumnAlignFirstMethodChain() { return columnAlignFirstMethodChain; }

    public boolean isIndentCaseInSwitch() {
        return indentCaseInSwitch;
    }


    /**
     * When true, all comments will be printed, unless printJavadoc is false, then only line and block comments will be
     * printed.
     */
    public PrettyPrinterConfiguration setPrintComments(boolean printComments) {
        this.printComments = printComments;
        return this;
    }

    /**
     * When true, Javadoc will be printed.
     */
    public PrettyPrinterConfiguration setPrintJavadoc(boolean printJavadoc) {
        this.printJavadoc = printJavadoc;
        return this;
    }

    /**
     * Set if there should be spaces between operators
     */
    public PrettyPrinterConfiguration setSpaceAroundOperators(boolean spaceAroundOperators){
        this.spaceAroundOperators = spaceAroundOperators;
        return this;
    }

    public PrettyPrinterConfiguration setColumnAlignParameters(boolean columnAlignParameters) {
        this.columnAlignParameters = columnAlignParameters;
        return this;
    }

    public PrettyPrinterConfiguration setColumnAlignFirstMethodChain(boolean columnAlignFirstMethodChain) {
        this.columnAlignFirstMethodChain = columnAlignFirstMethodChain;
        return this;
    }

    public PrettyPrinterConfiguration setIndentCaseInSwitch(boolean indentInSwitch) {
        this.indentCaseInSwitch = indentInSwitch;
        return this;
    }

    public Function<PrettyPrinterConfiguration, VoidVisitor<Void>> getVisitorFactory() {
        return visitorFactory;
    }

    /**
     * Set the factory that creates the PrettyPrintVisitor. By changing this you can make the PrettyPrinter use a custom
     * PrettyPrinterVisitor.
     */
    public PrettyPrinterConfiguration setVisitorFactory(Function<PrettyPrinterConfiguration, VoidVisitor<Void>> visitorFactory) {
        this.visitorFactory = assertNotNull(visitorFactory);
        return this;
    }

    public String getEndOfLineCharacter() {
        return endOfLineCharacter;
    }

    /**
     * Set the character to append when a line should end. Example values: "\n", "\r\n", "".
     */
    public PrettyPrinterConfiguration setEndOfLineCharacter(String endOfLineCharacter) {
        this.endOfLineCharacter = assertNotNull(endOfLineCharacter);
        return this;
    }

    /**
     * When true, orders imports by alphabetically.
     */
    public PrettyPrinterConfiguration setOrderImports(boolean orderImports) {
        this.orderImports = orderImports;
        return this;
    }



    public int getMaxEnumConstantsToAlignHorizontally() {
        return maxEnumConstantsToAlignHorizontally;
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
        this.maxEnumConstantsToAlignHorizontally = maxEnumConstantsToAlignHorizontally;
        return this;
    }
}
