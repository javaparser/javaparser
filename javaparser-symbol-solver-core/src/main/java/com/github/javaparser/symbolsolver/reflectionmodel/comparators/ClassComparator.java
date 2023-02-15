/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2023 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.reflectionmodel.comparators;

import java.util.Comparator;

/**
 * @author Federico Tomassetti
 */
public class ClassComparator implements Comparator<Class<?>> {

    @Override
    public int compare(Class<?> o1, Class<?> o2) {
        int subCompare;
        subCompare = o1.getCanonicalName().compareTo(o2.getCanonicalName());
        if (subCompare != 0) return subCompare;
        subCompare = Boolean.compare(o1.isAnnotation(), o2.isAnnotation());
        if (subCompare != 0) return subCompare;
        subCompare = Boolean.compare(o1.isArray(), o2.isArray());
        if (subCompare != 0) return subCompare;
        subCompare = Boolean.compare(o1.isEnum(), o2.isEnum());
        if (subCompare != 0) return subCompare;
        subCompare = Boolean.compare(o1.isInterface(), o2.isInterface());
        if (subCompare != 0) return subCompare;
        return 0;
    }
}
