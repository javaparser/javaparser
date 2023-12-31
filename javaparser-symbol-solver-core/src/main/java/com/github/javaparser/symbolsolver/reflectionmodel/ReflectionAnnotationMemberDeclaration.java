/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2024 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.reflectionmodel;

import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedAnnotationMemberDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedType;

import java.lang.annotation.Annotation;
import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.function.Function;

/**
 * @author Malte Skoruppa
 */
public class ReflectionAnnotationMemberDeclaration implements ResolvedAnnotationMemberDeclaration {

    private static Map<Class<?>, Function<Object, ? extends Expression>> valueAsExpressionConverters = new HashMap<>();
    static {
        valueAsExpressionConverters.put(Boolean.class, (value) -> new BooleanLiteralExpr((Boolean) value));
        valueAsExpressionConverters.put(Character.class, (value) -> new CharLiteralExpr((Character) value));
        valueAsExpressionConverters.put(Double.class, (value) -> new DoubleLiteralExpr((Double) value));
        valueAsExpressionConverters.put(Integer.class, (value) -> new IntegerLiteralExpr((Integer) value));
        valueAsExpressionConverters.put(Long.class, (value) -> new LongLiteralExpr((Long) value));
        valueAsExpressionConverters.put(String.class, (value) -> new StringLiteralExpr((String) value));
        valueAsExpressionConverters.put(Class.class, (value) -> {
            final ClassOrInterfaceType type = new ClassOrInterfaceType(null, ((Class<?>) value).getSimpleName());
            return new ClassExpr(type);
        });
    }
    
    private Method annotationMember;
    private TypeSolver typeSolver;

    public ReflectionAnnotationMemberDeclaration(Method annotationMember, TypeSolver typeSolver) {
        this.annotationMember = annotationMember;
        this.typeSolver = typeSolver;
    }

    @Override
    public Expression getDefaultValue() {
        Object value = annotationMember.getDefaultValue();
        if (value == null) return null;

        if (value.getClass().isArray()) {
            Object[] values = (Object[]) value;
            final NodeList<Expression> expressions = Arrays.stream(values)
                    .map(this::transformDefaultValue)
                    .collect(NodeList.toNodeList());
            return new ArrayInitializerExpr(expressions);
        }

        return transformDefaultValue(value);
    }

    private Expression transformDefaultValue(Object value) {
        if (value instanceof Enum<?>) {
            final Class<?> declaringClass = ((Enum<?>) value).getDeclaringClass();
            final String name = ((Enum<?>) value).name();
            return new FieldAccessExpr(new NameExpr(declaringClass.getSimpleName()), name);
        } else if (value instanceof Annotation) {
            final Class<? extends Annotation> annotationType = ((Annotation) value).annotationType();
            final Method[] declaredMethods = annotationType.getDeclaredMethods();
            final NodeList<MemberValuePair> pairs = Arrays.stream(declaredMethods)
                    .map(m -> {
                        final ReflectionAnnotationMemberDeclaration nestedMemberDeclaration = new ReflectionAnnotationMemberDeclaration(m, typeSolver);
                        return new MemberValuePair(m.getName(), nestedMemberDeclaration.getDefaultValue());
                    })
                    .collect(NodeList.toNodeList());

            return new NormalAnnotationExpr(new Name(annotationType.getSimpleName()), pairs);
        }

        Function<Object, ? extends Expression> fn = valueAsExpressionConverters.get(value.getClass());
        if (fn == null)
            throw new UnsupportedOperationException(
                    String.format("Obtaining the default value of the annotation member %s (of type %s) is not supported yet.",
                            annotationMember.getName(), value.getClass().getSimpleName())
            );
        return fn.apply(value);
    }

    @Override
    public ResolvedType getType() {
        Class returnType = annotationMember.getReturnType();
        if (returnType.isPrimitive()) {
            return ResolvedPrimitiveType.byName(returnType.getName());
        }
        SymbolReference<ResolvedReferenceTypeDeclaration> rrtd = typeSolver.tryToSolveType(returnType.getName());
        if (rrtd.isSolved()) {
            return new ReferenceTypeImpl(rrtd.getCorrespondingDeclaration());
        }
        throw new UnsupportedOperationException(String.format("Obtaining the type of the annotation member %s is not supported yet.", annotationMember.getName()));
    }

    @Override
    public String getName() {
        return annotationMember.getName();
    }
}
