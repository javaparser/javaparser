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

package com.github.javaparser.symbolsolver.resolution.typeinference;

import com.github.javaparser.resolution.types.ResolvedType;

import java.util.LinkedList;
import java.util.List;

/**
 * @author Federico Tomassetti
 */
public class InstantiationSet {

    private List<Instantiation> instantiations;

    public boolean allInferenceVariablesAreResolved(BoundSet boundSet) {
        throw new UnsupportedOperationException();
    }

    public static InstantiationSet empty() {
        return EMPTY;
    }

    private static final InstantiationSet EMPTY = new InstantiationSet();

    private InstantiationSet() {
        instantiations = new LinkedList<>();
    }

    public InstantiationSet withInstantiation(Instantiation instantiation) {
        InstantiationSet newInstance = new InstantiationSet();
        newInstance.instantiations.addAll(this.instantiations);
        newInstance.instantiations.add(instantiation);
        return newInstance;
    }

    public boolean isEmpty() {
        return instantiations.isEmpty();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        InstantiationSet that = (InstantiationSet) o;

        return instantiations.equals(that.instantiations);
    }

    @Override
    public int hashCode() {
        return instantiations.hashCode();
    }

    @Override
    public String toString() {
        return "InstantiationSet{" +
                "instantiations=" + instantiations +
                '}';
    }

    public ResolvedType apply(ResolvedType type) {
        for (Instantiation instantiation : instantiations) {
            type = type.replaceTypeVariables(instantiation.getInferenceVariable().getTypeParameterDeclaration(), instantiation.getProperType());
        }
        return type;
    }
}
