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
package com.github.javaparser;

/**
 * A range of characters in a source file, from "begin" to "end", including the characters at "begin" and "end".
 */
public class Range {

    public final Position begin;

    public final Position end;

    /**
     * A range of characters in a source file, from "begin" to "end".
     * This range is inclusive of the characters at the "begin" and "end" positions.
     * <p>
     * Note that if the given parameters are reversed (i.e. the end is earlier than begin, then the values are swapped.
     *
     * @param begin The starting position of the range.
     * @param end   The end position of the range.
     */
    public Range(Position begin, Position end) {
        if (begin == null) {
            throw new IllegalArgumentException("begin can't be null");
        }
        if (end == null) {
            throw new IllegalArgumentException("end can't be null");
        }
        // Force `begin` to be the position that is earliest within the document:
        if (begin.isBefore(end)) {
            this.begin = begin;
            this.end = end;
        } else {
            this.begin = end;
            this.end = begin;
        }
    }

    /**
     * Create a new `Range` object using the given begin and end position.
     *
     * @param begin The starting position of the range.
     * @param end   The end position of the range.
     * @return A new `Range` object with the given start/end position.
     */
    public static Range range(Position begin, Position end) {
        return new Range(begin, end);
    }

    /**
     * Create a new `Range` object using the given begin and end line/column values.
     * Valid values for each parameter are per the constructor of{@link Position}.
     *
     * @param beginLine   The start line of the range.
     * @param beginColumn The start line column of the range.
     * @param endLine     The end line of the range.
     * @param endColumn   The end column of the range.
     * @return A new `Range` object with the given start/end position.
     */
    public static Range range(int beginLine, int beginColumn, int endLine, int endColumn) {
        return new Range(new Position(beginLine, beginColumn), new Position(endLine, endColumn));
    }

    /**
     * @param beginColumn The value used to replace the current begin column number.
     *                    Valid values are per the constructor of{@link Position}.
     * @return A copy of this `Range` object, but with the begin column number replaced with the given column number.
     */
    public Range withBeginColumn(int beginColumn) {
        return range(begin.withColumn(beginColumn), end);
    }

    /**
     * @param beginLine The value used to replace the current begin line number.
     *                  Valid values are per the constructor of{@link Position}.
     * @return A copy of this `Range` object, but with the begin line number replaced with the given line number.
     */
    public Range withBeginLine(int beginLine) {
        return range(begin.withLine(beginLine), end);
    }

    /**
     * @param endColumn The value used to replace the current end column number.
     *                  Valid values are per the constructor of{@link Position}.
     * @return A copy of this `Range` object, but with the end column number replaced with the given line column.
     */
    public Range withEndColumn(int endColumn) {
        return range(begin, end.withColumn(endColumn));
    }

    /**
     * @param endLine The value used to replace the current end line number.
     *                Valid values are per the constructor of{@link Position}.
     * @return A copy of this `Range` object, but with the end line number replaced with the given line number.
     */
    public Range withEndLine(int endLine) {
        return range(begin, end.withLine(endLine));
    }

    /**
     * @param begin The value used to replace the current begin position.
     * @return A copy of this `Range` object, but with the begin position replaced with the given position.
     */
    public Range withBegin(Position begin) {
        return range(begin, this.end);
    }

    /**
     * @param end The value used to replace the current end position.
     * @return A copy of this `Range` object, but with the end position replaced with the given position.
     */
    public Range withEnd(Position end) {
        return range(this.begin, end);
    }

    /**
     * Does this loosely contain the other range?
     * <p>
     * As {@link #strictlyContains(Range)}, but also allow ranges which have an equal start and/or end position.
     * In these cases, the `other` range is not strictly "inside" of this range.
     */
    public boolean contains(Range other) {
        boolean beginResult = (begin.isBeforeOrEqual(other.begin));
        if (!beginResult)
            return false;
        return end.isAfterOrEqual(other.end);
    }

    /**
     * Does this loosely contain the other range?
     * <p>
     * As {@link #strictlyContains(Position)}, but a position that is on the "edge" of this range will also pass.
     * <p>
     * For example, if the given position is equal to the start or end position of this range.
     * In these cases, the `other` range is not strictly "inside" of this range.
     */
    public boolean contains(Position position) {
        return strictlyContains(position) || begin.equals(position) || end.equals(position);
    }

    /**
     * Does this strictly contain the other range?
     * <p>
     * It means that this has to be larger than other and it has to start before other and end after other.
     */
    public boolean strictlyContains(Range other) {
        boolean beginResult = (begin.isBefore(other.begin));
        boolean endResult = (end.isAfter(other.end));
        return beginResult && endResult;
    }

    /**
     * Does this strictly contain position.
     * <p>
     * It means that the position is after the begin of this range and before the end of this range.
     */
    public boolean strictlyContains(Position position) {
        return position.isAfter(begin) && position.isBefore(end);
    }

    /**
     * Does the other 'Range' overlap with this 'Range'?
     * <p>
     * If two ranges overlap, this range or the other range contains the begin or the end of the other range.
     * <p>
     * Note that if the ends are "touching" (i.e. a begin position == end position), this counts as an overlap
     * because the positions refer to characters, as opposed to boundary between characters.
     * <p>
     * For example, there is an overlap at "C" in the following ranges, with "C" existing within both ranges:
     * <pre>
     * Range 1: ABC
     * Range 2:   CDE</pre>
     */
    public boolean overlapsWith(Range other) {
        return (contains(other.begin) || contains(other.end)) || (other.contains(begin) || other.contains(end));
    }

    /**
     * @param position The position to compare against.
     * @return True if the end of this range is before (but not equal to) the given position to compare against.
     */
    public boolean isBefore(Position position) {
        return end.isBefore(position);
    }

    /**
     * @param other The range to compare against.
     * @return True if the end of this range is before (but not equal to) the given position to compare against.
     */
    public boolean isBefore(Range other) {
        return end.isBefore(other.begin);
    }

    /**
     * @param position The position to compare against.
     * @return True if the start of this range is after (but not equal to) the given position to compare against.
     */
    public boolean isAfter(Position position) {
        return begin.isAfter(position);
    }

    /**
     * @param other The range to compare against.
     * @return True if the start of this range is after (but not equal to) the given position to compare against.
     */
    public boolean isAfter(Range other) {
        return begin.isAfter(other.end);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o)
            return true;
        if (o == null || getClass() != o.getClass())
            return false;
        Range range = (Range) o;
        return begin.equals(range.begin) && end.equals(range.end);
    }

    @Override
    public int hashCode() {
        return 31 * begin.hashCode() + end.hashCode();
    }

    @Override
    public String toString() {
        return begin + "-" + end;
    }

    /**
     * @return The number of lines that this range represents.
     * <p>
     * If the start line and end line are the same, this range is limited to just one line.
     */
    public int getLineCount() {
        return end.line - begin.line + 1;
    }
}
