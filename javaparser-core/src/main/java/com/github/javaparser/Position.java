package com.github.javaparser;

import com.github.javaparser.ast.Node;

public class Position {
    public final int line;
    public final int column;

    public static final Position ABSOLUTE_START = new Position(Node.ABSOLUTE_BEGIN_LINE, -1);
    public static final Position ABSOLUTE_END = new Position(Node.ABSOLUTE_END_LINE, -1);

    /**
     * @deprecated Use node.getBegin()
     */
    @Deprecated
    public static Position beginOf(Node node) {
        return node.getBegin();
    }

    /**
     * @deprecated Use node.getEnd()
     */
    @Deprecated
    public static Position endOf(Node node) {
        return node.getEnd();
    }

    public Position(int line, int column) {
        this.line = line;
        this.column = column;
    }

    /**
     * @deprecated Use Position.line
     */
    @Deprecated
    public int getLine() {
        return this.line;
    }

    /**
     * @deprecated Use Position.column
     */
    @Deprecated
    public int getColumn() {
        return this.column;
    }

    public Position withLine(int line) {
        return new Position(line, this.column);
    }

    public Position withColumn(int column) {
        return new Position(this.line, column);
    }
}
