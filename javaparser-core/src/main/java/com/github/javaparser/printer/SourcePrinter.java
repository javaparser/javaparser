package com.github.javaparser.printer;

import static com.github.javaparser.utils.Utils.EOL;

class SourcePrinter {
    private final String indentation;
    private int level = 0;
    private boolean indented = false;
    private final StringBuilder buf = new StringBuilder();

    SourcePrinter(final String indentation) {
        this.indentation = indentation;
    }

    SourcePrinter indent() {
        level++;
        return this;
    }

    SourcePrinter unindent() {
        level--;
        return this;
    }

    private void makeIndent() {
        for (int i = 0; i < level; i++) {
            buf.append(indentation);
        }
    }

    SourcePrinter print(final String arg) {
        if (!indented) {
            makeIndent();
            indented = true;
        }
        buf.append(arg);
        return this;
    }

    SourcePrinter println(final String arg) {
        print(arg);
        println();
        return this;
    }

    SourcePrinter println() {
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
