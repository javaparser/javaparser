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

package com.github.javaparser.symbolsolver.javassistmodel;

import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedAnnotation;
import com.github.javaparser.resolution.declarations.ResolvedAnnotationDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedParameterDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import javassist.CtClass;
import javassist.bytecode.annotation.Annotation;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
public class JavassistParameterDeclaration implements ResolvedParameterDeclaration {
    private ResolvedType type;
    private TypeSolver typeSolver;
    private boolean variadic;
    private String name;

    private List<Annotation> annotations;

    public JavassistParameterDeclaration(CtClass type, TypeSolver typeSolver, boolean variadic, String name, List<Annotation> annotations) {
        this(JavassistFactory.typeUsageFor(type, typeSolver), typeSolver, variadic, name, annotations);
    }

    public JavassistParameterDeclaration(ResolvedType type, TypeSolver typeSolver, boolean variadic, String name, List<Annotation> annotations) {
        this.name = name;
        this.type = type;
        this.typeSolver = typeSolver;
        this.variadic = variadic;
        this.annotations = annotations;
    }

    @Override
    public String toString() {
        return "JavassistParameterDeclaration{" +
                "type=" + type +
                ", typeSolver=" + typeSolver +
                ", variadic=" + variadic +
                '}';
    }

    @Override
    public boolean hasName() {
        return name != null;
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public boolean isField() {
        return false;
    }

    @Override
    public boolean isParameter() {
        return true;
    }

    @Override
    public boolean isVariadic() {
        return variadic;
    }

    @Override
    public boolean isType() {
        return false;
    }

    @Override
    public ResolvedType getType() {
        return type;
    }

    @Override
    public List<ResolvedAnnotation> getAnnotations() {
        return annotations.stream().map(it -> new JavassistAnnotation(it, typeSolver)).collect(Collectors.toList());
    }

    @Override
    public Set<ResolvedAnnotationDeclaration> getDeclaredAnnotations() {
        return getAnnotations().stream().map(ResolvedAnnotation::getAnnotationType).collect(Collectors.toSet());
    }
}
