package com.github.javaparser;

import static com.github.javaparser.Position.pos;

/**
 * A range of characters in a source file, from "begin" to "end", including the characters at "begin" and "end".
 */
public class Range {
    public static final Range UNKNOWN = range(Position.UNKNOWN, Position.UNKNOWN);

    public final Position begin;
    public final Position end;

    public Range(Position begin, Position end) {
        if (begin == null) {
            throw new IllegalArgumentException("begin can't be null");
        }
        if (end == null) {
            throw new IllegalArgumentException("end can't be null");
        }
        this.begin = begin;
        this.end = end;
    }

    public Position getBegin() {
        return begin;
    }

    public Position getEnd() {
        return end;
    }

    public static Range range(Position begin, Position end) {
        return new Range(begin, end);
    }

    public static Range range(int beginLine, int beginColumn, int endLine, int endColumn) {
        return new Range(pos(beginLine, beginColumn), pos(endLine, endColumn));
    }

    public Range withBeginColumn(int column) {
        return range(begin.withColumn(column), end);
    }

    public Range withBeginLine(int line) {
        return range(begin.withLine(line), end);
    }

    public Range withEndColumn(int column) {
        return range(begin, end.withColumn(column));
    }

    public Range withEndLine(int line) {
        return range(begin, end.withLine(line));
    }

    public Range withBegin(Position begin) {
        return range(begin, this.end);
    }

    public Range withEnd(Position end) {
        return range(this.begin, end);
    }

    public boolean contains(Range other) {
        return begin.isBefore(other.begin) && end.isAfter(other.end);
    }

    public boolean isBefore(Position position) {
        return end.isBefore(position);
    }

    public boolean isAfter(Position position) {
        return begin.isAfter(position);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        Range range = (Range) o;

        if (begin != null ? !begin.equals(range.begin) : range.begin != null) return false;
        return end != null ? end.equals(range.end) : range.end == null;

    }

    @Override
    public int hashCode() {
        int result = begin != null ? begin.hashCode() : 0;
        result = 31 * result + (end != null ? end.hashCode() : 0);
        return result;
    }
}
