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

import com.github.javaparser.ast.NodeList;

import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.lang.reflect.TypeVariable;
import java.lang.reflect.WildcardType;
import java.util.Optional;

import static java.lang.reflect.Modifier.isAbstract;

/**
 * A hacky thing that collects flags we need from AST types to generate the metamodel.
 */
class AstTypeAnalysis {
    final boolean isAbstract;
    boolean isOptional = false;
    boolean isNodeList = false;
    boolean isSelfType = false;
    Class<?> innerType;

    AstTypeAnalysis(Type type) {
        if (type instanceof Class<?>) {
            TypeVariable<? extends Class<?>>[] typeParameters = ((Class<?>) type).getTypeParameters();
            if (typeParameters.length > 0) {
                isSelfType = true;
            }
        } else {
            while (type instanceof ParameterizedType) {
                ParameterizedType t = (ParameterizedType) type;
                Type currentOuterType = t.getRawType();
                if (currentOuterType == NodeList.class) {
                    isNodeList = true;
                }
                if (currentOuterType == Optional.class) {
                    isOptional = true;
                }

                if (t.getActualTypeArguments()[0] instanceof WildcardType) {
                    type = t.getRawType();
                    isSelfType = true;
                    break;
                }
                type = t.getActualTypeArguments()[0];
            }
        }
        innerType = (Class<?>) type;
        isAbstract = isAbstract(innerType.getModifiers());
    }
}
