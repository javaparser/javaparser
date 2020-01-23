/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2020 The JavaParser Team.
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

package org.javaparser.ast.nodeTypes;

import org.javaparser.ast.Node;
import org.javaparser.ast.NodeList;
import org.javaparser.ast.type.ClassOrInterfaceType;

import static org.javaparser.StaticJavaParser.parseClassOrInterfaceType;

/**
 * A node that extends other types.
 */
public interface NodeWithExtends<N extends Node> {
    NodeList<ClassOrInterfaceType> getExtendedTypes();

    void tryAddImportToParentCompilationUnit(Class<?> clazz);

    default ClassOrInterfaceType getExtendedTypes(int i) {
        return getExtendedTypes().get(i);
    }

    N setExtendedTypes(NodeList<ClassOrInterfaceType> extendsList);

    @SuppressWarnings("unchecked")
    default N setExtendedType(int i, ClassOrInterfaceType extend) {
        getExtendedTypes().set(i, extend);
        return (N) this;
    }

    @SuppressWarnings("unchecked")
    default N addExtendedType(ClassOrInterfaceType extend) {
        getExtendedTypes().add(extend);
        return (N) this;
    }

    /**
     * @deprecated use addExtendedType
     */
    default N addExtends(Class<?> clazz) {
        return addExtendedType(clazz);
    }

    /**
     * @deprecated use addExtendedType
     */
    default N addExtends(String name) {
        return addExtendedType(name);
    }

    /**
     * Add an "extends" to this and automatically add the import
     *
     * @param clazz the class to extand from
     * @return this
     */
    default N addExtendedType(Class<?> clazz) {
        tryAddImportToParentCompilationUnit(clazz);
        return addExtendedType(clazz.getSimpleName());
    }

    /**
     * Add an "extends" to this
     *
     * @param name the name of the type to extends from
     * @return this
     */
    @SuppressWarnings("unchecked")
    default N addExtendedType(String name) {
        getExtendedTypes().add(parseClassOrInterfaceType(name));
        return (N) this;
    }
}
