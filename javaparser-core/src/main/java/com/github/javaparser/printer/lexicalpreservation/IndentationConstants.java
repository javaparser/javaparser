/*
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
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
package com.github.javaparser.printer.lexicalpreservation;

/**
 * Constants related to indentation management in lexical preservation.
 *
 * This class centralizes all indentation-related constants to avoid duplication
 * and ensure consistency across IndentationContext and IndentationCalculator.
 */
public final class IndentationConstants {

    /**
     * Standard indentation size in spaces.
     * This is the number of spaces added or removed when increasing/decreasing indentation.
     */
    public static final int STANDARD_INDENTATION_SIZE = 4;

    /**
     * Private constructor to prevent instantiation.
     * This is a constants class and should not be instantiated.
     */
    private IndentationConstants() {
        throw new AssertionError("IndentationConstants is a constants class and should not be instantiated");
    }
}
