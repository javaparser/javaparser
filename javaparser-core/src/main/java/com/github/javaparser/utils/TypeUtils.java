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

import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.type.VoidType;

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
        String descriptor;
        if (clazz == Void.TYPE) {
            descriptor = new VoidType().toDescriptor();
        } else if (clazz == Integer.TYPE) {
            descriptor = PrimitiveType.intType().toDescriptor();
        } else if (clazz == Boolean.TYPE) {
            descriptor = PrimitiveType.booleanType().toDescriptor();
        } else if (clazz == Byte.TYPE) {
            descriptor = PrimitiveType.byteType().toDescriptor();
        } else if (clazz == Character.TYPE) {
            descriptor = PrimitiveType.charType().toDescriptor();
        } else if (clazz == Short.TYPE) {
            descriptor = PrimitiveType.shortType().toDescriptor();
        } else if (clazz == Double.TYPE) {
            descriptor = PrimitiveType.doubleType().toDescriptor();
        } else if (clazz == Float.TYPE) {
            descriptor = PrimitiveType.floatType().toDescriptor();
        } else if (clazz == Long.TYPE) {
            descriptor = PrimitiveType.longType().toDescriptor();
        } else {
            throw new AssertionError("Unknown primitive: " + clazz.getName());
        }
        return descriptor;
    }
}
