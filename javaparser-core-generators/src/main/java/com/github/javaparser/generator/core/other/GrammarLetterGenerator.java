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

package com.github.javaparser.generator.core.other;

import java.util.function.Function;

/**
 * Prints the LETTER and PART_LETTER tokens. They should be inserted into the grammar manually.
 */
public class GrammarLetterGenerator {
    public static void main(String[] args) {
        generate("LETTER", c -> Character.isJavaIdentifierStart(c) || Character.isHighSurrogate((char) (int) c) || Character.isLowSurrogate((char) (int) c));
        generate("PART_LETTER", c -> Character.isJavaIdentifierPart(c) || Character.isHighSurrogate((char) (int) c) || Character.isLowSurrogate((char) (int) c));
    }

    private static void generate(String tokenName, Function<Integer, Boolean> f) {
        final String indent = "         ";
        System.out.println("  < #" + tokenName + ": [");
        System.out.print(indent);
        int nltime = 0;
        int i = 0;
        while (i < 0x10000) {
            while (!f.apply(i) && i < 0x10000) {
                i++;
            }
            String start = format(i);
            while (f.apply(i) && i < 0x10000) {
                i++;
            }
            String end = format(i - 1);
            if (i >= 0x10000) {
                break;
            }
            if (start.equals(end)) {
                nltime++;
                System.out.print(start + ",  ");
            } else {
                nltime += 2;
                System.out.print(start + "-" + end + ",  ");
            }
            if (nltime >= 10) {
                nltime = 0;
                System.out.println();
                System.out.print(indent);
            }
        }
        // Too lazy to remove the final illegal comma.
        System.out.println("]");
        System.out.println("        | <UNICODE_ESCAPE>");
        System.out.println("  >");
    }

    private static String format(int i) {
        return String.format("\"\\u%04x\"", i);
    }
}
