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
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.metamodel.DerivedProperty;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * A node which has a list of variables.
 */
public interface NodeWithVariables<N extends Node> {
    NodeList<VariableDeclarator> getVariables();

    N setVariables(NodeList<VariableDeclarator> variables);

    default VariableDeclarator getVariable(int i) {
        return getVariables().get(i);
    }

    @SuppressWarnings("unchecked")
    default N setVariable(int i, VariableDeclarator variableDeclarator) {
        getVariables().set(i, variableDeclarator);
        return (N) this;
    }

    @SuppressWarnings("unchecked")
    default N addVariable(VariableDeclarator variableDeclarator) {
        getVariables().add(variableDeclarator);
        return (N) this;
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
     * <br/>For <code>int a,b;</code>, then doing setType(String) on b, then calling getElementType(). This is an assertion error. It is also a situation that you don't really want.
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

    /**
     * Sets the type of all variables.
     * Erases any existing type.
     * This is a shortcut for setting a type on all variable declarators separately.
     */
    @SuppressWarnings("unchecked")
    default N setAllTypes(Type newType) {
        for (VariableDeclarator variable : getVariables()) {
            variable.setType(newType);
        }
        return (N) this;
    }

    /**
     * Returns the type that maximum shared type between all variables.
     * The minimum common type does never include annotations on the array level.
     * <p>
     * <br/>For <code>int a;</code> this is int.
     * <br/>For <code>int a,b,c,d;</code> this is also int.
     * <br/>For <code>int a,b[],c;</code> this is also int.
     * <br/>For <code>int[] a[][],b[],c[][];</code> this is int[][].
     */
    @DerivedProperty
    default Optional<Type> getMaximumCommonType() {
        return calculateMaximumCommonType(getVariables().stream().map(v -> v.getType()).collect(Collectors.toList()));
    }

    static Optional<Type> calculateMaximumCommonType(List<Type> types) {
        // we use a local class because we cannot use an helper static method in an interface
        class Helper {
            // Conceptually: given a type we start from the Element Type and get as many array levels as indicated
            // From the implementation point of view we start from the actual type and we remove how many array
            // levels as needed to get the target level of arrays
            // It returns null if the type has less array levels then the desired target
            private Optional<Type> toArrayLevel(Type type, int level) {
                if (level > type.getArrayLevel()) {
                    return Optional.empty();
                }
                for (int i = type.getArrayLevel(); i > level; i--) {
                    if (!(type instanceof ArrayType)) {
                        return Optional.empty();
                    }
                    type = ((ArrayType) type).getComponentType();
                }
                return Optional.of(type);
            }
        }

        Helper helper = new Helper();
        int level = 0;
        boolean keepGoing = true;
        // In practice we want to check for how many levels of arrays all the variables have the same type,
        // including also the annotations
        while (keepGoing) {
            final int currentLevel = level;
            // Now, given that equality on nodes consider the position the simplest way is to compare
            // the pretty-printed string got for a node. We just check all them are the same and if they
            // are we just just is not null
            Object[] values = types.stream().map(v -> {
                Optional<Type> t = helper.toArrayLevel(v, currentLevel);
                return t.map(Node::toString).orElse(null);
            }).distinct().toArray();
            if (values.length == 1 && values[0] != null) {
                level++;
            } else {
                keepGoing = false;
            }
        }
        return helper.toArrayLevel(types.get(0), --level);
    }

}
