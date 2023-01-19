/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

package com.github.javaparser.generator.metamodel;

import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.stmt.Statement;

import java.lang.annotation.Annotation;
import java.lang.reflect.Constructor;
import java.lang.reflect.Field;

import static com.github.javaparser.StaticJavaParser.parseStatement;
import static com.github.javaparser.generator.metamodel.MetaModelGenerator.nodeMetaModelFieldName;
import static com.github.javaparser.generator.metamodel.MetaModelGenerator.propertyMetaModelFieldName;
import static com.github.javaparser.utils.CodeGenerationUtils.f;

class InitializeConstructorParametersStatementsGenerator {
    void generate(Class<? extends Node> nodeClass, NodeList<Statement> initializeConstructorParametersStatements) {
        if (nodeClass == Node.class) {
            return;
        }
        Constructor<?> constructor = findAllFieldsConstructor(nodeClass);
        for (java.lang.reflect.Parameter parameter : constructor.getParameters()) {
            Field field = findFieldInClass(nodeClass, parameter.getName());

            String addFieldStatement = f("%s.getConstructorParameters().add(%s.%s);",
                    nodeMetaModelFieldName(nodeClass),
                    nodeMetaModelFieldName(field.getDeclaringClass()),
                    propertyMetaModelFieldName(field));

            initializeConstructorParametersStatements.add(parseStatement(addFieldStatement));
        }
    }

    private Field findFieldInClass(Class<?> nodeClass, String name) {
        Class<?> searchClass = nodeClass;
        do {
            for (Field field : searchClass.getDeclaredFields()) {
                if (field.getName().equals(name)) {
                    return field;
                }
            }
            searchClass = searchClass.getSuperclass();
        } while (searchClass != null);
        throw new AssertionError(f("Couldn't find constructor parameter %s as a field, class %s", name, nodeClass.getSimpleName()));
    }

    private Constructor<?> findAllFieldsConstructor(Class<? extends Node> nodeClass) {
        for (Constructor<?> constructor : nodeClass.getDeclaredConstructors()) {
            for (Annotation annotation : constructor.getAnnotations()) {
                if (annotation.annotationType() == AllFieldsConstructor.class) {
                    return constructor;
                }
            }
        }
        throw new AssertionError(f("Node class %s has no constructor annotated with @AllFieldsConstructor", nodeClass.getSimpleName()));
    }
}
