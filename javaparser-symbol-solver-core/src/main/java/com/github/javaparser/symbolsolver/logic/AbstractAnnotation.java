/*
 *
 *  * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 *  * Copyright (C) 2011, 2013-2023 The JavaParser Team.
 *  *
 *  * This file is part of JavaParser.
 *  *
 *  * JavaParser can be used either under the terms of
 *  * a) the GNU Lesser General Public License as published by
 *  *     the Free Software Foundation, either version 3 of the License, or
 *  *     (at your option) any later version.
 *  * b) the terms of the Apache License
 *  *
 *  * You should have received a copy of both licenses in LICENCE.LGPL and
 *  * LICENCE.APACHE. Please refer to those files for details.
 *  *
 *  * JavaParser is distributed in the hope that it will be useful,
 *  * but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  * GNU Lesser General Public License for more details.
 *
 */

package com.github.javaparser.symbolsolver.logic;

import com.github.javaparser.resolution.declarations.ResolvedAnnotation;
import com.github.javaparser.resolution.declarations.ResolvedAnnotationDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedAnnotationMemberDeclaration;

import java.util.HashMap;
import java.util.Map;

public abstract class AbstractAnnotation implements ResolvedAnnotation {

    private ResolvedAnnotationDeclaration cachedType;

    protected abstract ResolvedAnnotationDeclaration calculateAnnotationType();

    @Override
    public Map<String, Object> getAnnotationMembersNameValueMap() {
        Map<String, Object> tempMap = new HashMap<>();

        for (Map.Entry<ResolvedAnnotationMemberDeclaration, Object> tempEntry : getAnnotationMemberValueMap().entrySet()) {
            tempMap.put(tempEntry.getKey().getName(), tempEntry.getValue());
        }

        return tempMap;
    }

    @Override
    public ResolvedAnnotationDeclaration getAnnotationType() {
        if (cachedType == null) {
            cachedType = calculateAnnotationType();
        }
        return cachedType;
    }
}
