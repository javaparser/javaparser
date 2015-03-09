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

package com.github.javaparser.ast.lexical;

import java.util.EnumSet;

/**
 * @author Didier Villevalois
 */
public class Separator extends Lexeme {

    private final SeparatorKind kind;

    public Separator(SeparatorKind kind) {
        super();
        this.kind = kind;
    }

    @Override
    public LexemeKind getLexemeKind() {
        return LexemeKind.SEPARATOR;
    }

    public SeparatorKind getSeparatorKind() {
        return kind;
    }

    @Override
    public boolean is(SeparatorKind first, SeparatorKind... rest) {
        return EnumSet.of(first, rest).contains(getSeparatorKind());
    }

    @Override
    public String image() {
        return kind.image;
    }
}
