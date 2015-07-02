/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2015 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with JavaParser.  If not, see <http://www.gnu.org/licenses/>.
 */

package com.github.javaparser.full.utils;

import com.github.javaparser.ast.Node;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.List;

/**
 * A normalized JSON writer. We write commas (',') even for the last name/value pairs and array elements. This is to
 * better support GIT diffs.
 *
 * @author Didier Villevalois
 */
public class NormalizedJsonWriter {

    public static final String INDENT_STRING = "  ";
    private final StringBuilder builder;

    public NormalizedJsonWriter(StringBuilder builder) {
        this.builder = builder;
    }

    public static String write(Node node) {
        StringBuilder builder = new StringBuilder();
        NormalizedJsonWriter writer = new NormalizedJsonWriter(builder);
        writer.writeNode(node);
        return builder.toString();
    }

    public void writeNode(Node node) {
        writeNode(node, 0);
        builder.append("\n");
    }

    private void writeNode(Node node, int indent) {
        Class<? extends Node> nodeClass = node.getClass();
        String className = nodeClass.getName();

        builder.append("{\n");

        writeField("class", String.class, className, indent + 1);

        writeFields(node, nodeClass, indent + 1);

        writeIndent(indent);
        builder.append("}");
    }

    private void writeFields(Node node, Class<? extends Node> nodeClass, int indent) {
        Class<?> superclass = nodeClass.getSuperclass();
        if (Node.class.isAssignableFrom(superclass)) {
            writeFields(node, superclass.asSubclass(Node.class), indent);
        }

        for (Field field : nodeClass.getDeclaredFields()) {
            if (Modifier.isStatic(field.getModifiers())) continue;

            String fieldName = field.getName();
            Class<?> fieldType = field.getType();

            if (fieldName.equals("parentNode") || fieldName.equals("childrenNodes")) continue;

            try {
                field.setAccessible(true);
                writeField(fieldName, fieldType, field.get(node), indent);
            } catch (IllegalAccessException e) {
                e.printStackTrace(); // FIXME
            }
        }
    }

    private void writeField(String fieldName, Class<?> valueClass, Object value, int indent) {
        writeIndent(indent);
        builder.append(fieldName);
        builder.append(": ");
        writeValue(valueClass, value, indent);
        builder.append(",\n");
    }

    private void writeValue(Class<?> valueClass, Object value, int indent) {
        if (value == null) {
            builder.append("null");
        } else {
            if (valueClass.isPrimitive() ||
                    String.class.isAssignableFrom(valueClass) ||
                    Enum.class.isAssignableFrom(valueClass)) {
                builder.append(value.toString());
            } else if (valueClass.isArray()) {
                writeArray(valueClass.getComponentType(), (Object[]) value, indent);
            } else if (List.class.isAssignableFrom(valueClass)) {
                List<?> list = (List<?>) value;
                Class<?> elementClass = list.isEmpty() ? Object.class : list.get(0).getClass();
                writeArray(elementClass, list.toArray(), indent);
            } else if (Node.class.isAssignableFrom(valueClass)) {
                writeNode((Node) value, indent);
            }
        }
    }

    private void writeArray(Class<?> valueClass, Object[] values, int indent) {
        builder.append("[\n");

        for (Object value : values) {
            writeIndent(indent + 1);
            writeValue(valueClass, value, indent + 1);
            builder.append(",\n");
        }

        writeIndent(indent);
        builder.append("]");
    }

    private void writeIndent(int indent) {
        for (int i = 0; i < indent; i++) {
            builder.append(INDENT_STRING);
        }
    }
}
