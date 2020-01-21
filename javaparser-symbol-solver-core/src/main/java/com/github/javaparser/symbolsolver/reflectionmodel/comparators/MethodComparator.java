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

package com.github.javaparser.symbolsolver.reflectionmodel.comparators;

import java.lang.reflect.Method;
import java.util.Comparator;

/**
 * @author Federico Tomassetti
 */
public class MethodComparator implements Comparator<Method> {

    @Override
    public int compare(Method o1, Method o2) {
        int compareName = o1.getName().compareTo(o2.getName());
        if (compareName != 0) return compareName;
        int compareNParams = o1.getParameterCount() - o2.getParameterCount();
        if (compareNParams != 0) return compareNParams;
        for (int i = 0; i < o1.getParameterCount(); i++) {
            int compareParam = new ParameterComparator().compare(o1.getParameters()[i], o2.getParameters()[i]);
            if (compareParam != 0) return compareParam;
        }
        int compareResult = new ClassComparator().compare(o1.getReturnType(), o2.getReturnType());
        if (compareResult != 0) return compareResult;
        return 0;
    }
}
