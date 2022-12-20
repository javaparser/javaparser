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
            String descriptor;
            if (currentClass == Void.TYPE) {
                descriptor = new VoidType().toDescriptor();
            } else if (currentClass == Integer.TYPE) {
                descriptor = PrimitiveType.intType().toDescriptor();
            } else if (currentClass == Boolean.TYPE) {
                descriptor = PrimitiveType.booleanType().toDescriptor();
            } else if (currentClass == Byte.TYPE) {
                descriptor = PrimitiveType.byteType().toDescriptor();
            } else if (currentClass == Character.TYPE) {
                descriptor = PrimitiveType.charType().toDescriptor();
            } else if (currentClass == Short.TYPE) {
                descriptor = PrimitiveType.shortType().toDescriptor();
            } else if (currentClass == Double.TYPE) {
                descriptor = PrimitiveType.doubleType().toDescriptor();
            } else if (currentClass == Float.TYPE) {
                descriptor = PrimitiveType.floatType().toDescriptor();
            } else if (currentClass == Long.TYPE) {
                descriptor = PrimitiveType.longType().toDescriptor();
            } else {
                throw new AssertionError("Unknown primitive: " + currentClass.getName());
            }
            stringBuilder.append(descriptor);
        } else {
            stringBuilder.append("L").append(currentClass.getName().replace(".", "/")).append(";");
        }
    }
}
