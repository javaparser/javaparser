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

package com.github.javaparser.resolution.types;

import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * A union type is defined in java as list of types separates by pipes.
 *
 * @author Federico Tomassetti
 */
public class ResolvedUnionType implements ResolvedType {
    private List<ResolvedType> elements;

    public ResolvedUnionType(List<ResolvedType> elements) {
        if (elements.size() < 2) {
            throw new IllegalArgumentException("An union type should have at least two elements. This has " + elements.size());
        }
        this.elements = new LinkedList<>(elements);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        ResolvedUnionType that = (ResolvedUnionType) o;

        return new HashSet<>(elements).equals(new HashSet<>(that.elements));
    }

    @Override
    public int hashCode() {
        return new HashSet<>(elements).hashCode();
    }

    @Override
    public String describe() {
        return String.join(" | ", elements.stream().map(ResolvedType::describe).collect(Collectors.toList()));
    }

    @Override
    public boolean isAssignableBy(ResolvedType other) {
        return elements.stream().allMatch(e -> e.isAssignableBy(other));
    }

    @Override
    public boolean isUnionType() {
        return true;
    }

    @Override
    public ResolvedUnionType asUnionType() {
        return this;
    }
}
