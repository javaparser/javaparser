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

import static com.github.javaparser.utils.Utils.assertNotNull;
import java.util.Objects;

/**
 * A position in a source file. Lines and columns start counting at 1.
 */
public class Position implements Comparable<Position> {

    public final int line;

    public final int column;

    /**
     * The first line -- note that it is 1-indexed (i.e. the first line is line 1, as opposed to 0)
     */
    public static final int FIRST_LINE = 1;

    /**
     * The first column -- note that it is 1-indexed (i.e. the first column is column 1, as opposed to 0)
     */
    public static final int FIRST_COLUMN = 1;

    /**
     * The first position in the file.
     */
    public static final Position HOME = new Position(FIRST_LINE, FIRST_COLUMN);

    /**
     * Line numbers must be positive, thus
     */
    public static final int ABSOLUTE_BEGIN_LINE = -1;

    public static final int ABSOLUTE_END_LINE = -2;

    /**
     * TODO: Do we refer to the characters as columns,
     *  ...or the spaces between (thus also before/after) characters as columns?
     */
    public Position(int line, int column) {
        if (line < Position.ABSOLUTE_END_LINE) {
            throw new IllegalArgumentException("Can't position at line " + line);
        }
        if (column < -1) {
            // TODO: This allows/permits column 0, which seemingly contradicts first column being 1
            // ... (see also nextLine() which indicates 1 being the first column of the next line)
            // ... (see also valid() which requires a column > 0)
            // TODO: Maybe we need an "ABSOLUTE_BEGIN_LINE" and "ABSOLUTE_END_LINE"?
            throw new IllegalArgumentException("Can't position at column " + column);
        }
        this.line = line;
        this.column = column;
    }

    /**
     * Convenient factory method.
     *
     * @deprecated Use the constructor (e.g. {@code new Position(line, column)})
     */
    @Deprecated
    public static Position pos(int line, int column) {
        return new Position(line, column);
    }

    /**
     * @return Jump to the given column number, while retaining the current line number.
     */
    public Position withColumn(int column) {
        return new Position(this.line, column);
    }

    /**
     * @return Jump to the given line number, while retaining the current column number.
     */
    public Position withLine(int line) {
        return new Position(line, this.column);
    }

    /**
     * @return a position that is "characters" characters more to the right than this position.
     */
    public Position right(int characters) {
        return new Position(line, this.column + characters);
    }

    /**
     * @return a position that is on the start of the next line from this position.
     */
    public Position nextLine() {
        return new Position(line + 1, FIRST_COLUMN);
    }

    /**
     * Check if the position is usable,
     * also checks for special positions (ABSOLUTE_BEGIN_LINE and ABSOLUTE_END_LINE).
     * Does not know what it is pointing at, so it can't check if the position is after the end of the source.
     * @return true if the position is usable or a special position.
     */
    public boolean valid() {
        return ABSOLUTE_END_LINE == line || ABSOLUTE_BEGIN_LINE == line || line >= FIRST_LINE && column >= FIRST_COLUMN;
    }

    /**
     * @see #valid()
     * @return The inverse of {@link #valid()}
     */
    public boolean invalid() {
        return !valid();
    }

    /**
     * @return If this position is valid, this.
     *   Otherwise, if the alternativePosition is valid, return that.
     *   Otherwise, just return this.
     */
    public Position orIfInvalid(Position alternativePosition) {
        assertNotNull(alternativePosition);
        if (this.valid()) {
            return this;
        }
        return alternativePosition.valid() ? alternativePosition : this;
    }

    /**
     * @param otherPosition the other position to compare to
     * @return true if this position is after the given position
     */
    public boolean isAfter(Position otherPosition) {
        assertNotNull(otherPosition);
        if (line == otherPosition.line) {
            return column > otherPosition.column;
        }
        return line > otherPosition.line || otherPosition.line == Position.ABSOLUTE_BEGIN_LINE;
    }

    public boolean isAfterOrEqual(Position otherPosition) {
        return isAfter(otherPosition) || equals(otherPosition);
    }

    /**
     * @param otherPosition the other position to compare to
     * @return true if this position is before the given position
     */
    public boolean isBefore(Position otherPosition) {
        assertNotNull(otherPosition);
        if (line == otherPosition.line) {
            return column < otherPosition.column;
        }
        return line < otherPosition.line || otherPosition.line == Position.ABSOLUTE_END_LINE;
    }

    public boolean isBeforeOrEqual(Position otherPosition) {
        return isBefore(otherPosition) || equals(otherPosition);
    }

    @Override
    public int compareTo(Position otherPosition) {
        assertNotNull(otherPosition);
        if (isBefore(otherPosition)) {
            return -1;
        }
        if (isAfter(otherPosition)) {
            return 1;
        }
        return 0;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o)
            return true;
        if (o == null || getClass() != o.getClass())
            return false;
        Position otherPosition = (Position) o;
        return Objects.equals(line, otherPosition.line) && Objects.equals(column, otherPosition.column);
    }

    @Override
    public int hashCode() {
        return Objects.hash(line, column);
    }

    @Override
    public String toString() {
        return "(line " + line + ",col " + column + ")";
    }
}
