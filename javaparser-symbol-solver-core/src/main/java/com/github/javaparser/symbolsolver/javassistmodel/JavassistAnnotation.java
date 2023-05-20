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

package com.github.javaparser.symbolsolver.javassistmodel;

import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedAnnotationDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedAnnotationMemberDeclaration;
import com.github.javaparser.symbolsolver.logic.AbstractAnnotation;
import javassist.bytecode.annotation.Annotation;

import java.util.*;

import static com.github.javaparser.symbolsolver.javassistmodel.JavassistUtils.computeMemberValue;

public class JavassistAnnotation extends AbstractAnnotation {

    private Annotation annotation;

    private TypeSolver typeSolver;

    public JavassistAnnotation(Annotation annotation, TypeSolver typeSolver) {
        this.annotation = annotation;
        this.typeSolver = typeSolver;
    }

    @Override
    protected ResolvedAnnotationDeclaration calculateAnnotationType() {
        return (ResolvedAnnotationDeclaration) typeSolver.solveType(annotation.getTypeName());
    }

    @Override
    public Map<ResolvedAnnotationMemberDeclaration, Object> getAnnotationMemberValueMap() {
        Map<ResolvedAnnotationMemberDeclaration, Object> tempMap = new HashMap<>();

        Set<String> tempNames = annotation.getMemberNames();
        if (tempNames == null) return Collections.emptyMap();
        ResolvedAnnotationDeclaration tempAnnotationType = getAnnotationType();

        for (String tempName : tempNames) {
            ResolvedAnnotationMemberDeclaration tempMemberDecl = tempAnnotationType.getAnnotationMembers().stream().filter(it -> Objects.equals(it.getName(), tempName)).findFirst().orElseThrow(() -> new IllegalStateException("Can not find annotation member " + tempName + " in type " + tempAnnotationType.getQualifiedName()));
            tempMap.put(tempMemberDecl, computeMemberValue(annotation.getMemberValue(tempName), typeSolver));
        }

        return tempMap;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        JavassistAnnotation that = (JavassistAnnotation) o;

        return annotation.equals(that.annotation);
    }

    @Override
    public int hashCode() {
        return annotation.hashCode();
    }
}
