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
package com.github.javaparser.resolution.types;

/**
 * The special type void.
 *
 * @author Federico Tomassetti
 */
public class ResolvedVoidType implements ResolvedType {

    public static final ResolvedType INSTANCE = new ResolvedVoidType();

    private ResolvedVoidType() {
    }

    @Override
    public String describe() {
        return "void";
    }

    @Override
    public boolean isAssignableBy(ResolvedType other) {
        // According to https://docs.oracle.com/javase/specs/jls/se16/html/jls-14.html#jls-14.8:
        // """
        // Note that the Java programming language does not allow a "cast to void" - void is not a type - so the
        // traditional C trick of writing an expression statement such as:
        //
        // (void)... ;  // incorrect!
        //
        // does not work.
        // """
        //
        // In short, nothing can be assign to "void".
        return false;
    }

    @Override
    public boolean isVoid() {
        return true;
    }

    @Override
    public String toDescriptor() {
        return "V";
    }
}
