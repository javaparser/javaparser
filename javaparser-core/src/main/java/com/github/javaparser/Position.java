/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2015 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with JavaParser.  If not, see <http://www.gnu.org/licenses/>.
 */

package com.github.javaparser;

import com.github.javaparser.ast.Node;

public class Position implements Comparable<Position> {
    private int line;
    private int column;

    public static final Position ABSOLUTE_START = new Position(Node.ABSOLUTE_BEGIN_LINE,-1);
    public static final Position ABSOLUTE_END = new Position(Node.ABSOLUTE_END_LINE,-1);

    public static Position beginOf(Node node){
        return new Position(node.getBeginColumn(),node.getBeginColumn());
    }

    public static Position endOf(Node node){
        return new Position(node.getEndColumn(),node.getEndColumn());
    }

    public Position(int line, int column){
        this.line = line;
        this.column = column;
    }

    public int getLine(){
        return this.line;
    }

    public int getColumn(){
        return this.column;
    }

    @Override
    public int compareTo(Position o) {
        return this.line != o.line ? this.line - o.line : this.column - o.column;
    }
}
