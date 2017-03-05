/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
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

import static com.github.javaparser.utils.Utils.EOL;

public class SourcePrinter {
    private final String indentation;
    private int level = 0;
    private boolean indented = false;
    private final StringBuilder buf = new StringBuilder();

    SourcePrinter(final String indentation) {
        this.indentation = indentation;
    }

    public SourcePrinter indent() {
        level++;
        return this;
    }

    public SourcePrinter unindent() {
        level--;
        return this;
    }

    private void makeIndent() {
        for (int i = 0; i < level; i++) {
            buf.append(indentation);
        }
    }

    public SourcePrinter print(final String arg) {
        if (!indented) {
            makeIndent();
            indented = true;
        }
        buf.append(arg);
        return this;
    }

    public SourcePrinter println(final String arg) {
        print(arg);
        println();
        return this;
    }

    public SourcePrinter println() {
        buf.append(EOL);
        indented = false;
        return this;
    }

    public String getSource() {
        return buf.toString();
    }

    @Override
    public String toString() {
        return getSource();
    }
}
