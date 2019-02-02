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

package com.github.javaparser;

import static com.github.javaparser.Position.pos;

/**
 * A range of characters in a source file, from "begin" to "end", including the characters at "begin" and "end".
 */
public class Range {
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

    /**
     * As strictlyContains, but two exactly matching ranges are also considered contained one in each other.
     */
    public boolean contains(Range other) {
        return (begin.isBefore(other.begin) || begin.equals(other.begin)) &&
                (end.isAfter(other.end) || end.equals(other.end));
    }

    /**
     * Do this strictly contains other? It means that this has to be larger than other and it has to start as other
     * or before and end as other or after.
     */
    public boolean strictlyContains(Range other) {
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

    public int getLineCount() {
        return end.line - begin.line + 1;
    }
}
