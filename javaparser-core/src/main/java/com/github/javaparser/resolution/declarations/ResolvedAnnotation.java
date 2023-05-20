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

package com.github.javaparser.resolution.declarations;

import com.github.javaparser.resolution.types.ResolvedType;

import java.util.Map;

public interface ResolvedAnnotation {

    /**
     * The type of the annotation
     */
    ResolvedAnnotationDeclaration getAnnotationType();

    /**
     * Works like {@link ResolvedAnnotation#getAnnotationMemberValueMap()} but converts the {@link ResolvedAnnotationMemberDeclaration} to its names.
     */
    Map<String, Object> getAnnotationMembersNameValueMap();

    /**
     * Returns a map of all members actually declared in this annotation (no members with only default values are included).
     * The values can either be a primitive (or its wrapper classes), a {@link String}, a {@link ResolvedTypeDeclaration}, a {@link ResolvedType}, {@link ResolvedEnumConstantDeclaration} or an array of those types.
     */
    Map<ResolvedAnnotationMemberDeclaration, Object> getAnnotationMemberValueMap();
}
