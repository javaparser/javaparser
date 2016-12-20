/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
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

package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.type.ClassOrInterfaceType;

/**
 * A node that extends other types.
 */
public interface NodeWithExtends<N extends Node> {
    NodeList<ClassOrInterfaceType> getExtendedTypes();

    default ClassOrInterfaceType getExtendedTypes(int i) {
        return getExtendedTypes().get(i);
    }

    N setExtendedTypes(NodeList<ClassOrInterfaceType> extendsList);

    /**
     * Add an extends to this and automatically add the import
     *
     * @param clazz the class to extand from
     * @return this
     */
    default N addExtends(Class<?> clazz) {
        ((Node) this).tryAddImportToParentCompilationUnit(clazz);
        return addExtends(clazz.getSimpleName());
    }

    /**
     * Add an extends to this
     *
     * @param name the name of the type to extends from
     * @return this
     */
    @SuppressWarnings("unchecked")
    default N addExtends(String name) {
        ClassOrInterfaceType classOrInterfaceType = new ClassOrInterfaceType(name);
        getExtendedTypes().add(classOrInterfaceType);
        classOrInterfaceType.setParentNode((Node) this);
        return (N) this;
    }
}
