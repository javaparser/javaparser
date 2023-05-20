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

package com.github.javaparser.symbolsolver.reflectionmodel;

import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedAnnotationDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedAnnotationMemberDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedEnumDeclaration;
import com.github.javaparser.symbolsolver.logic.AbstractAnnotation;

import java.lang.annotation.Annotation;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.HashMap;
import java.util.Map;
import java.util.stream.Stream;

public class ReflectionAnnotation extends AbstractAnnotation {

    private Annotation annotation;

    private TypeSolver typeSolver;

    public ReflectionAnnotation(Annotation annotation, TypeSolver typeSolver) {
        this.annotation = annotation;
        this.typeSolver = typeSolver;
    }

    @Override
    protected ResolvedAnnotationDeclaration calculateAnnotationType() {
        return (ResolvedAnnotationDeclaration) ReflectionFactory.typeDeclarationFor(annotation.getClass(), typeSolver);
    }

    @Override
    public Map<ResolvedAnnotationMemberDeclaration, Object> getAnnotationMemberValueMap() {
        Map<ResolvedAnnotationMemberDeclaration, Object> tempMap = new HashMap<>();

        Class<? extends Annotation> tempType = annotation.annotationType();
        for (Method tempMethod : tempType.getDeclaredMethods()) {
            try {
                Object tempResult = ReflectionFactory.convertAnnotationMemberValue(tempMethod.invoke(annotation), typeSolver);
                tempMap.put(new ReflectionAnnotationMemberDeclaration(tempMethod, typeSolver), tempResult);
            } catch (IllegalAccessException | InvocationTargetException e) {
                throw new IllegalStateException("Could not read annotation value of " + tempMethod.getName() + " via reflection from " + tempType.getName(), e);
            }
        }

        return tempMap;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        ReflectionAnnotation that = (ReflectionAnnotation) o;

        return annotation.equals(that.annotation);
    }

    @Override
    public int hashCode() {
        return annotation.hashCode();
    }
}
