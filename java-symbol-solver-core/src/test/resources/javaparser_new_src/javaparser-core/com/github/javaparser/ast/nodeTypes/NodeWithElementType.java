/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2015 The JavaParser Team.
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

import com.github.javaparser.ast.ArrayBracketPair;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.Type;

import java.util.List;

/**
 * A node having an element type.
 * In most cases, the element type is simply the type.
 * In case of arrays, the element type is the type that is inside the deepest nesting:
 * for int[][][], the element type is int.
 *
 * The main reason for this interface is to permit users to manipulate homogeneously all nodes with getElementType/setElementType
 * methods
 */
public interface NodeWithElementType<T> {
    /**
     * @return the element type
     */
    Type<?> getElementType();

    /**
     * @param elementType the element elementType
     * @return this
     */
    T setElementType(Type<?> elementType);

    List<ArrayBracketPair> getArrayBracketPairsAfterElementType();

    T setArrayBracketPairsAfterElementType(List<ArrayBracketPair> arrayBracketPairsAfterType);

    /**
     * Sets this type to this class and try to import it to the {@link CompilationUnit} if needed
     * 
     * @param typeClass the type
     * @return this
     */
    default T setElementType(Class<?> typeClass) {
        ((Node) this).tryAddImportToParentCompilationUnit(typeClass);
        return setElementType(new ClassOrInterfaceType(typeClass.getSimpleName()));
    }

    default T setElementType(final String type) {
        ClassOrInterfaceType classOrInterfaceType = new ClassOrInterfaceType(type);
        return setElementType(classOrInterfaceType);
    }
}
