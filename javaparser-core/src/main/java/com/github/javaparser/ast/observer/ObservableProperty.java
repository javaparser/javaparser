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
import java.util.Collection;
import java.util.Optional;
import static com.github.javaparser.ast.observer.ObservableProperty.Type.*;

/**
 * Properties considered by the AstObserver
 */
public enum ObservableProperty {

    ANNOTATIONS(Type.MULTIPLE_REFERENCE), ANONYMOUS_CLASS_BODY(Type.MULTIPLE_REFERENCE), ARGUMENTS(Type.MULTIPLE_REFERENCE), ASTERISK(Type.SINGLE_ATTRIBUTE), BODY(Type.SINGLE_REFERENCE), CATCH_CLAUSES(Type.MULTIPLE_REFERENCE), CHECK(Type.SINGLE_REFERENCE), CLASS_BODY(Type.MULTIPLE_REFERENCE), CLASS_DECLARATION(Type.SINGLE_REFERENCE), CLASS_EXPR(Type.SINGLE_REFERENCE), COMMENT(Type.SINGLE_REFERENCE), COMPARE(Type.SINGLE_REFERENCE), COMPONENT_TYPE(Type.SINGLE_REFERENCE), CONDITION(Type.SINGLE_REFERENCE), CONTENT(Type.SINGLE_ATTRIBUTE), DEFAULT(Type.SINGLE_ATTRIBUTE), DEFAULT_VALUE(Type.SINGLE_REFERENCE), DIMENSION(Type.SINGLE_REFERENCE), ELEMENTS(Type.MULTIPLE_REFERENCE), ELEMENT_TYPE(Type.SINGLE_REFERENCE), ELSE_EXPR(Type.SINGLE_REFERENCE), ELSE_STMT(Type.SINGLE_REFERENCE), ENCLOSING_PARAMETERS(Type.SINGLE_ATTRIBUTE), ENTRIES(Type.MULTIPLE_REFERENCE), EXPRESSION(Type.SINGLE_REFERENCE), EXTENDED_TYPE(Type.SINGLE_REFERENCE), EXTENDED_TYPES(Type.MULTIPLE_REFERENCE), FINALLY_BLOCK(Type.SINGLE_REFERENCE), IDENTIFIER(Type.SINGLE_ATTRIBUTE), IMPLEMENTED_TYPES(Type.MULTIPLE_REFERENCE), IMPORTS(Type.MULTIPLE_REFERENCE), INDEX(Type.SINGLE_REFERENCE), INITIALIZATION(Type.MULTIPLE_REFERENCE), INITIALIZER(Type.SINGLE_REFERENCE), INNER(Type.SINGLE_REFERENCE), INTERFACE(Type.SINGLE_ATTRIBUTE), ITERABLE(Type.SINGLE_REFERENCE), LABEL(Type.SINGLE_REFERENCE), LEFT(Type.SINGLE_REFERENCE), LEVELS(Type.MULTIPLE_REFERENCE), MEMBERS(Type.MULTIPLE_REFERENCE), MEMBER_VALUE(Type.SINGLE_REFERENCE), MESSAGE(Type.SINGLE_REFERENCE), MODIFIERS(Type.MULTIPLE_ATTRIBUTE), NAME(Type.SINGLE_REFERENCE), OPERATOR(Type.SINGLE_ATTRIBUTE), PACKAGE_DECLARATION(Type.SINGLE_REFERENCE), PAIRS(Type.MULTIPLE_REFERENCE), PARAMETER(Type.SINGLE_REFERENCE), PARAMETERS(Type.MULTIPLE_REFERENCE), QUALIFIER(Type.SINGLE_REFERENCE), RESOURCES(Type.MULTIPLE_REFERENCE), RIGHT(Type.SINGLE_REFERENCE), SCOPE(Type.SINGLE_REFERENCE), SELECTOR(Type.SINGLE_REFERENCE), STATEMENT(Type.SINGLE_REFERENCE), STATEMENTS(Type.MULTIPLE_REFERENCE), STATIC(Type.SINGLE_ATTRIBUTE), SUPER_TYPE(Type.SINGLE_REFERENCE), TARGET(Type.SINGLE_REFERENCE), THEN_EXPR(Type.SINGLE_REFERENCE), THEN_STMT(Type.SINGLE_REFERENCE), THIS(Type.SINGLE_ATTRIBUTE), THROWN_EXCEPTIONS(Type.MULTIPLE_REFERENCE), TRY_BLOCK(Type.SINGLE_REFERENCE), TYPE(Type.SINGLE_REFERENCE), TYPES(Type.MULTIPLE_REFERENCE), TYPE_ARGUMENTS(Type.MULTIPLE_REFERENCE), TYPE_BOUND(Type.MULTIPLE_REFERENCE), TYPE_PARAMETERS(Type.MULTIPLE_REFERENCE), UPDATE(Type.MULTIPLE_REFERENCE), VALUE(Type.SINGLE_REFERENCE), VALUES(Type.MULTIPLE_REFERENCE), VARIABLE(Type.SINGLE_REFERENCE), VARIABLES(Type.MULTIPLE_REFERENCE), VAR_ARGS(Type.SINGLE_ATTRIBUTE), ELSE_BLOCK(Type.SINGLE_ATTRIBUTE, true), EXPRESSION_BODY(Type.SINGLE_REFERENCE, true), MAXIMUM_COMMON_TYPE(Type.SINGLE_REFERENCE, true), POSTFIX(Type.SINGLE_ATTRIBUTE, true), PREFIX(Type.SINGLE_ATTRIBUTE, true), THEN_BLOCK(Type.SINGLE_ATTRIBUTE, true), USING_DIAMOND_OPERATOR(Type.SINGLE_ATTRIBUTE, true), RANGE, COMMENTED_NODE;

    enum Type {

        SINGLE_ATTRIBUTE(false, false), SINGLE_REFERENCE(false, true), MULTIPLE_ATTRIBUTE(true, false), MULTIPLE_REFERENCE(true, true);

        private boolean multiple;

        private boolean node;

        Type(boolean multiple, boolean node) {
            this.multiple = multiple;
            this.node = node;
        }
    }

    private Type type;

    private boolean derived;

    ObservableProperty(Type type) {
        this.type = type;
        this.derived = false;
    }

    ObservableProperty(Type type, boolean derived) {
        this.type = type;
        this.derived = derived;
    }

    ObservableProperty() {
        this(Type.SINGLE_REFERENCE, false);
    }

    public boolean isAboutNodes() {
        return type.node;
    }

    public boolean isAboutValues() {
        return !isAboutNodes();
    }

    public boolean isMultiple() {
        return type.multiple;
    }

    public boolean isSingle() {
        return !isMultiple();
    }

    public String camelCaseName() {
        return Utils.toCamelCase(name());
    }

    public Node singlePropertyFor(Node node) {
        String getterName = "get" + Utils.capitalize(camelCaseName());
        try {
            Object result = node.getClass().getMethod(getterName).invoke(node);
            if (result == null) {
                return null;
            }
            if (result instanceof Node) {
                return (Node) result;
            } else if (result instanceof Optional) {
                Optional<Node> opt = (Optional<Node>) result;
                if (opt.isPresent()) {
                    return opt.get();
                } else {
                    return null;
                }
            } else {
                throw new RuntimeException(String.format("Property %s returned %s (%s)", this.name(), result.toString(), result.getClass().getCanonicalName()));
            }
        } catch (IllegalAccessException | InvocationTargetException | NoSuchMethodException e) {
            throw new RuntimeException("Unable to get single value for " + this.name() + " from " + node, e);
        } catch (ClassCastException e) {
            throw new RuntimeException(e);
        }
    }

    private boolean hasMethod(Node node, String name) {
        try {
            node.getClass().getMethod(name);
            return true;
        } catch (NoSuchMethodException e) {
            return false;
        }
    }

    public Object singleValueFor(Node node) {
        String getterName = "get" + Utils.capitalize(camelCaseName());
        if (!hasMethod(node, getterName)) {
            getterName = "has" + Utils.capitalize(camelCaseName());
            if (!hasMethod(node, getterName)) {
                if (camelCaseName().startsWith("is")) {
                    getterName = camelCaseName();
                } else {
                    getterName = "is" + Utils.capitalize(camelCaseName());
                }
            }
        }
        try {
            Object result = node.getClass().getMethod(getterName).invoke(node);
            if (result == null) {
                return null;
            }
            if (result instanceof Optional) {
                Optional<Node> opt = (Optional<Node>) result;
                if (opt.isPresent()) {
                    return opt.get();
                } else {
                    return null;
                }
            } else {
                return result;
            }
        } catch (IllegalAccessException | InvocationTargetException | NoSuchMethodException e) {
            throw new RuntimeException("Unable to get single value for " + this.name() + " from " + node + " (class: " + node.getClass().getSimpleName() + ")", e);
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
                return (NodeList) result;
            } else {
                Optional<NodeList> opt = (Optional<NodeList>) result;
                if (opt.isPresent()) {
                    return opt.get();
                } else {
                    return null;
                }
            }
        } catch (IllegalAccessException | InvocationTargetException | NoSuchMethodException e) {
            throw new RuntimeException("Unable to get list value for " + this.name() + " from " + node + " (class: " + node.getClass().getSimpleName() + ")", e);
        }
    }

    public Collection<?> listPropertyFor(Node node) {
        String getterName = "get" + Utils.capitalize(camelCaseName());
        try {
            Object result = node.getClass().getMethod(getterName).invoke(node);
            if (result == null) {
                return null;
            }
            return (Collection) result;
        } catch (IllegalAccessException | InvocationTargetException | NoSuchMethodException e) {
            throw new RuntimeException("Unable to get list value for " + this.name() + " from " + node + " (class: " + node.getClass().getSimpleName() + ")", e);
        }
    }

    public String singleStringValueFor(Node node) {
        String getterName = "get" + Utils.capitalize(camelCaseName());
        try {
            return (String) node.getClass().getMethod(getterName).invoke(node);
        } catch (IllegalAccessException | InvocationTargetException | NoSuchMethodException e) {
            throw new RuntimeException("Unable to get single value for " + this.name() + " from " + node, e);
        }
    }

    public boolean isNull(Node node) {
        String getterName = "get" + Utils.capitalize(camelCaseName());
        try {
            return null == node.getClass().getMethod(getterName).invoke(node);
        } catch (IllegalAccessException | InvocationTargetException | NoSuchMethodException e) {
            throw new RuntimeException("Unable to get single value for " + this.name() + " from " + node, e);
        }
    }

    public boolean isNullOrEmpty(Node node) {
        String getterName = "get" + Utils.capitalize(camelCaseName());
        try {
            Object result = node.getClass().getMethod(getterName).invoke(node);
            return null == result || ((result instanceof Optional) && !((Optional) result).isPresent());
        } catch (IllegalAccessException | InvocationTargetException | NoSuchMethodException e) {
            throw new RuntimeException("Unable to get single value for " + this.name() + " from " + node, e);
        }
    }
}

