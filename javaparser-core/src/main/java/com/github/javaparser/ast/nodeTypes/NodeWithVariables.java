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

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.Type;

import java.lang.reflect.Array;
import java.util.Comparator;

/**
 * A node which has a list of variables.
 */
public interface NodeWithVariables<N extends Node> {
    NodeList<VariableDeclarator> getVariables();

    N setVariables(NodeList<VariableDeclarator> variables);

    default VariableDeclarator getVariable(int i) {
        return getVariables().get(i);
    }

    /**
     * Returns the type that is shared between all variables.
     * This is a shortcut for when you are certain that all variables share one type.
     * What makes this difficult is arrays, and being able to set the type.
     * <br/>For <code>int a;</code> this is int.
     * <br/>For <code>int a,b,c,d;</code> this is also int.
     * <br/>For <code>int a,b[],c;</code> this is an assertion error since b is an int[], not an int.
     * <br/>For <code>int a,b;</code>, then doing setType(String) on b, this is an assertion error. It is also a situation that you don't really want.
     */
    default Type getCommonType() {
        NodeList<VariableDeclarator> variables = getVariables();
        if (variables.isEmpty()) {
            throw new AssertionError("There is no common type since there are no variables.");
        }
        Type type = variables.get(0).getType();
        for (int i = 1; i < variables.size(); i++) {
            if (!variables.get(i).getType().equals(type)) {
                throw new AssertionError("The variables do not have a common type.");
            }
        }
        return type;
    }

    /**
     * Returns the element type.
     * <br/>For <code>int a;</code> this is int.
     * <br/>For <code>int a,b,c,d;</code> this is also int.
     * <br/>For <code>int a,b[],c;</code> this is also int. Note: no mention of b being an array.
     * <br/>For <code>int a,b;</code>, then doing setType(String) on b, this is an assertion error. It is also a situation that you don't really want.
     */
    default Type getElementType() {
        NodeList<VariableDeclarator> variables = getVariables();
        if (variables.isEmpty()) {
            throw new AssertionError("There is no element type since there are no variables.");
        }
        Type type = variables.get(0).getType().getElementType();
        for (int i = 1; i < variables.size(); i++) {
            if (!variables.get(i).getType().getElementType().equals(type)) {
                throw new AssertionError("The variables do not have a common type.");
            }
        }
        return type;
    }

}
