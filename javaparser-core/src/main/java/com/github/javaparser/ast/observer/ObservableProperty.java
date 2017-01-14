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
package com.github.javaparser.ast.observer;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.utils.Utils;

import java.lang.reflect.InvocationTargetException;
import java.util.Optional;

import static com.github.javaparser.utils.Utils.capitalize;

/**
 * Properties considered by the AstObserver
 */
public enum ObservableProperty {
    ANNOTATIONS,
    ANONYMOUS_CLASS_BODY,
    ARGUMENTS,
    BLOCK,
    BODY,
    CATCH_CLAUSES,
    CHECK,
    CLASS_BODY,
    CLASS_EXPR,
    COMMENT,
    COMMENTED_NODE,
    COMPARE,
    COMPONENT_TYPE,
    CONDITION,
    CONTENT,
    DEFAULT_VALUE,
    DIMENSION,
    ELEMENTS,
    ELSE_EXPR,
    ELSE_STMT,
    ENTRIES,
    EXPRESSION,
    EXTENDED_TYPES,
    FIELD,
    FINALLY_BLOCK,
    IDENTIFIER,
    IMPLEMENTED_TYPES,
    IMPORTS,
    INDEX,
    INITIALIZER,
    INNER,
    IS_INTERFACE,
    ITERABLE,
    IS_THIS,
    LABEL,
    LEFT,
    LEVELS,
    MEMBERS,
    MEMBER_VALUE,
    MODIFIERS,
    MESSAGE,
    NAME,
    OPERATOR,
    PACKAGE_DECLARATION,
    PAIRS,
    PARAMETER,
    PARAMETERS,
    ENCLOSING_PARAMETERS,
    QUALIFIER,
    RANGE,
    RESOURCES,
    RIGHT,
    SCOPE,
    SELECTOR,
    IS_ASTERISK,
    IS_STATIC,
    STATIC_MEMBER,
    STATEMENT,
    STATEMENTS,
    SUPER,
    TARGET,
    THEN_EXPR,
    THEN_STMT,
    THROWN_TYPES,
    TRY_BLOCK,
    TYPE,
    TYPES,
    TYPE_ARGUMENTS,
    TYPE_BOUND,
    CLASS_DECLARATION,
    TYPE_PARAMETERS,
    UPDATE,
    VALUE,
    VALUES,
    VARIABLE,
    VARIABLES,
    ELEMENT_TYPE,
    VAR_ARGS;

    public String camelCaseName() {
        return Utils.toCamelCase(name());
    }

    public Node singleValueFor(Node node) {
        String getterName = "get" + Utils.capitalize(camelCaseName());
        try {
            Object result = node.getClass().getMethod(getterName).invoke(node);
            if (result == null) {
                return null;
            }
            if (result instanceof Node) {
                return (Node)result;
            } else {
                Optional<Node> opt = (Optional<Node>)result;
                if (opt.isPresent()) {
                    return opt.get();
                } else {
                    return null;
                }
            }
        } catch (IllegalAccessException | InvocationTargetException | NoSuchMethodException e) {
            throw new RuntimeException("Unable to get single value for " + this.name() + " from " + node, e);
        }
    }

    public NodeList<? extends Node> listValueFor(Node node) {
        String getterName = "get" + Utils.capitalize(camelCaseName());
        try {
            Object result = node.getClass().getMethod(getterName).invoke(node);
            if (result == null) {
                return null;
            }
            if (result instanceof NodeList) {
                return (NodeList)result;
            } else {
                Optional<NodeList> opt = (Optional<NodeList>)result;
                if (opt.isPresent()) {
                    return opt.get();
                } else {
                    return null;
                }
            }
        } catch (IllegalAccessException | InvocationTargetException | NoSuchMethodException e) {
            throw new RuntimeException("Unable to get list value for " + this.name() + " from " + node, e);
        }
    }

    public String singleStringValueFor(Node node) {
        String getterName = "get" + Utils.capitalize(camelCaseName());
        try {
            return (String)node.getClass().getMethod(getterName).invoke(node);
        } catch (IllegalAccessException | InvocationTargetException | NoSuchMethodException e) {
            throw new RuntimeException("Unable to get single value for " + this.name() + " from " + node, e);
        }
    }

}

