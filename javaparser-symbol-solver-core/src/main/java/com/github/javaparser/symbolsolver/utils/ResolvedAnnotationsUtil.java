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

package com.github.javaparser.symbolsolver.utils;

import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedAnnotation;
import com.github.javaparser.resolution.declarations.ResolvedAnnotationDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserAnnotation;
import com.github.javaparser.symbolsolver.javassistmodel.JavassistAnnotation;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionAnnotation;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionFactory;
import javassist.CtBehavior;
import javassist.CtClass;
import javassist.CtField;
import javassist.bytecode.AnnotationsAttribute;

import java.lang.annotation.Annotation;
import java.lang.reflect.AnnotatedElement;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class ResolvedAnnotationsUtil {

    public static List<? extends ResolvedAnnotation> getAnnotations(NodeWithAnnotations<?> wrappedNode, TypeSolver typeSolver) {
        NodeList<AnnotationExpr> tempAnnotations = wrappedNode.getAnnotations();
        return tempAnnotations.stream().map(ann -> new JavaParserAnnotation(ann, typeSolver)).collect(Collectors.toList());
    }

    public static Set<ResolvedAnnotationDeclaration> getDeclaredAnnotations(NodeWithAnnotations<?> wrappedNode) {
        return wrappedNode.getAnnotations().stream().map(AnnotationExpr::resolve).collect(Collectors.toSet());
    }

    public static List<? extends JavassistAnnotation> getAnnotations(CtBehavior ctBehavior, TypeSolver typeSolver) {
        AnnotationsAttribute visibleAnnotations = (AnnotationsAttribute) ctBehavior.getMethodInfo().getAttribute(AnnotationsAttribute.visibleTag);

        if (visibleAnnotations != null) {
            return Arrays.stream(visibleAnnotations.getAnnotations()).map(ann -> new JavassistAnnotation(ann, typeSolver)).collect(Collectors.toList());
        } else {
            return Collections.emptyList();
        }
    }

    public static Set<ResolvedAnnotationDeclaration> getDeclaredAnnotations(CtBehavior ctBehavior, TypeSolver typeSolver) {
        AnnotationsAttribute visibleAnnotations = (AnnotationsAttribute) ctBehavior.getMethodInfo().getAttribute(AnnotationsAttribute.visibleTag);

        if (visibleAnnotations != null) {
            return Arrays.stream(visibleAnnotations.getAnnotations()).map(ann -> (ResolvedAnnotationDeclaration) typeSolver.solveType(ann.getTypeName())).collect(Collectors.toSet());
        } else {
            return Collections.emptySet();
        }
    }

    public static List<? extends JavassistAnnotation> getAnnotations(CtClass ctClass, TypeSolver typeSolver) {
        AnnotationsAttribute visibleAnnotations = (AnnotationsAttribute) ctClass.getClassFile().getAttribute(AnnotationsAttribute.visibleTag);

        if (visibleAnnotations != null) {
            return Arrays.stream(visibleAnnotations.getAnnotations()).map(ann -> new JavassistAnnotation(ann, typeSolver)).collect(Collectors.toList());
        } else {
            return Collections.emptyList();
        }
    }

    public static Set<ResolvedAnnotationDeclaration> getDeclaredAnnotations(CtClass ctClass, TypeSolver typeSolver) {
        AnnotationsAttribute visibleAnnotations = (AnnotationsAttribute) ctClass.getClassFile().getAttribute(AnnotationsAttribute.visibleTag);

        if (visibleAnnotations != null) {
            return Arrays.stream(visibleAnnotations.getAnnotations()).map(ann -> (ResolvedAnnotationDeclaration) typeSolver.solveType(ann.getTypeName())).collect(Collectors.toSet());
        } else {
            return Collections.emptySet();
        }
    }

    public static List<? extends JavassistAnnotation> getAnnotations(CtField ctField, TypeSolver typeSolver) {
        AnnotationsAttribute visibleAnnotations = (AnnotationsAttribute) ctField.getFieldInfo().getAttribute(AnnotationsAttribute.visibleTag);

        if (visibleAnnotations != null) {
            return Arrays.stream(visibleAnnotations.getAnnotations()).map(ann -> new JavassistAnnotation(ann, typeSolver)).collect(Collectors.toList());
        } else {
            return Collections.emptyList();
        }
    }

    public static Set<ResolvedAnnotationDeclaration> getDeclaredAnnotations(CtField ctField, TypeSolver typeSolver) {
        AnnotationsAttribute visibleAnnotations = (AnnotationsAttribute) ctField.getFieldInfo().getAttribute(AnnotationsAttribute.visibleTag);

        if (visibleAnnotations != null) {
            return Arrays.stream(visibleAnnotations.getAnnotations()).map(ann -> (ResolvedAnnotationDeclaration) typeSolver.solveType(ann.getTypeName())).collect(Collectors.toSet());
        } else {
            return Collections.emptySet();
        }
    }

    public static List<? extends ReflectionAnnotation> getAnnotations(AnnotatedElement reflectionObject, TypeSolver typeSolver) {
        return Arrays.stream(reflectionObject.getAnnotations()).map(ann -> new ReflectionAnnotation(ann, typeSolver)).collect(Collectors.toList());
    }

    public static Set<ResolvedAnnotationDeclaration> getDeclaredAnnotations(AnnotatedElement reflectionObject, TypeSolver typeSolver) {
        return Arrays.stream(reflectionObject.getAnnotations()).map(Annotation::getClass).map(clazz -> (ResolvedAnnotationDeclaration) ReflectionFactory.typeDeclarationFor(clazz, typeSolver)).collect(Collectors.toSet());
    }
}
