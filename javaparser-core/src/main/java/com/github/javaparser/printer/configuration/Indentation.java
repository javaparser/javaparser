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

/**
 * This class defines the characteristics of an indentation: the type (space, tabs..) and the size (How many characters must be used to indent the code).
 */
public class Indentation {

    public enum IndentType {

        /**
         * Indent with spaces.
         */
        SPACES(' ', 1),
        /**
         * Indent with tabs as far as possible.
         * For proper aligning, the tab width is necessary and by default 4.
         */
        TABS('\t', 4),
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
        TABS_WITH_SPACE_ALIGN('\t', 4);

        private Character car;

        private int width;

        private IndentType(Character c, int width) {
            this.car = c;
            this.width = width;
        }

        public Character getCar() {
            return car;
        }

        public int getWidth() {
            return width;
        }
    }

    // default size
    private static final int DEFAULT_SIZE = 4;

    // type of the indentation
    private IndentType type;

    // size of the indentation (define how many spaces or tabs is used to indent)
    private int size;

    // formatted indentation
    private String formattedIndentation = "";

    /*
     * Creates an Indentation with a type and size
     */
    public Indentation(IndentType type, int size) {
        this.type = type;
        this.size = size;
        format();
    }

    /*
     * Creates an Indentation with the default size
     */
    public Indentation(IndentType type) {
        this(type, DEFAULT_SIZE);
    }

    /*
     * set the size of the indentation (how many spaces or tabs?)
     */
    public Indentation setSize(int size) {
        this.size = size;
        format();
        return this;
    }

    public int getSize() {
        return size;
    }

    /*
     * set the type of the indentation (spaces, tabs...)
     */
    public Indentation setType(IndentType type) {
        this.type = type;
        format();
        return this;
    }

    public IndentType getType() {
        return type;
    }

    /*
     * returns the formatted string that represents the identification
     */
    public String getIndent() {
        return formattedIndentation;
    }

    // format the indentation string
    private void format() {
        StringBuilder indentString = new StringBuilder();
        char indentChar = type.car;
        for (int i = 0; i < size; i++) {
            indentString.append(indentChar);
        }
        formattedIndentation = indentString.toString();
    }

    @Override
    public String toString() {
        return type.name() + " size=" + size;
    }
}
