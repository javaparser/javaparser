/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2020 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.model.resolution;

import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;

/**
 * Any type of value.
 *
 * @author Federico Tomassetti
 */
public class Value {
    private ResolvedType type;
    private String name;

    public Value(ResolvedType type, String name) {
        this.type = type;
        this.name = name;
    }

    /**
     * Create a Value from a ValueDeclaration.
     */
    public static Value from(ResolvedValueDeclaration decl) {
        ResolvedType type = decl.getType();
        return new Value(type, decl.getName());
    }

    @Override
    public String toString() {
        return "Value{" +
                "type=" + type +
                ", name='" + name + '\'' +
                '}';
    }

    public String getName() {
        return name;
    }

    public ResolvedType getType() {
        return type;
    }

}
