/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2022 The JavaParser Team.
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
package com.github.javaparser.utils;

import java.lang.reflect.Method;
import java.util.Optional;

import com.github.javaparser.ast.type.PrimitiveType.Primitive;
import com.github.javaparser.ast.type.VoidType;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedType;

public class TypeUtils {

    /*
     * Returns the method descriptor (https://docs.oracle.com/javase/specs/jvms/se8/html/jvms-4.html#jvms-4.3.3)
     * The method descriptor for the method: {@code Object m(int i, double d, Thread t) {...}}
     * is {@code (IDLjava/lang/Thread;)Ljava/lang/Object;}
     * Note that the internal forms of the binary names of Thread and Object are used.
     */
    public static String getMethodDescriptor(Method method) {
        StringBuilder stringBuilder = new StringBuilder();
        stringBuilder.append("(");
        for (Class<?> parameter : method.getParameterTypes()) {
            appendDescriptor(parameter, stringBuilder);
        }
        stringBuilder.append(")");
        appendDescriptor(method.getReturnType(), stringBuilder);
        return stringBuilder.toString();
    }

    private static void appendDescriptor(final Class<?> clazz, final StringBuilder stringBuilder) {
        Class<?> currentClass = clazz;
        while (currentClass.isArray()) {
            stringBuilder.append("[");
            currentClass = currentClass.getComponentType();
        }
        if (currentClass.isPrimitive()) {
            String descriptor = getPrimitiveTypeDescriptor(currentClass);
            stringBuilder.append(descriptor);
        } else {
            stringBuilder.append("L").append(currentClass.getName().replace(".", "/")).append(";");
        }
    }

    public static String getPrimitiveTypeDescriptor(final Class<?> clazz) {
        if (clazz == Void.TYPE || clazz == Void.class) {
            return new VoidType().toDescriptor();
        }
        String className = clazz.getCanonicalName();
        Optional<Primitive> prim = getPrimitive(className);
        if (prim.isPresent()) {
            return prim.get().toDescriptor();
        }
        Optional<ResolvedType> rt = ResolvedPrimitiveType.byBoxTypeQName(className);
        if (rt.isPresent()) {
            return getResolvedPrimitiveTypeDescriptor(rt);
        }
        throw new IllegalArgumentException("Unknown primitive: " + className);
    }

    private static String getResolvedPrimitiveTypeDescriptor(Optional<ResolvedType> rt) throws AssertionError {
        String typeName = rt.get().asPrimitive().describe();
        Optional<Primitive> prim = getPrimitive(typeName);
        return prim.map(p -> p.toDescriptor())
                .orElseThrow(() -> new AssertionError(
                        String.format(
                                "ResolvedPrimitiveType name \"%s\" does not match any Primitive enum constant identifier.",
                                typeName.toUpperCase())));
    }

    private static Optional<Primitive> getPrimitive(String name) {
        try {
            return Optional.of(Primitive.valueOf(name.toUpperCase()));
        } catch (IllegalArgumentException e) {
            return Optional.empty();
        }
    }
}
