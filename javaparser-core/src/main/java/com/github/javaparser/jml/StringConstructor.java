package com.github.javaparser.jml;

public class StringConstructor {

    private final StringBuilder sb = new StringBuilder(1024);

    // JavaCC starts with 1/1
    private int curLine = 1;

    private int curColumn = 1;

    public StringConstructor append(String value) {
        sb.ensureCapacity(sb.length() + value.length() + 1);
        for (char c : value.toCharArray()) {
            sb.append(c);
            if (c == '\n') {
                curColumn = 1;
                curLine++;
            } else {
                curColumn++;
            }
        }
        return this;
    }

    public StringConstructor expandTo(int line, int column) {
        if (curLine > line || (curLine == line && curColumn > column)) {
            throw new IllegalArgumentException();
        }
        for (; curLine < line; curLine++) {
            sb.append("\n");
            curColumn = 1;
        }
        for (; curColumn < column; curColumn++) {
            sb.append(" ");
        }
        return this;
    }

    @Override
    public String toString() {
        return sb.toString();
    }

    public StringBuilder getBuffer() {
        return sb;
    }
}
