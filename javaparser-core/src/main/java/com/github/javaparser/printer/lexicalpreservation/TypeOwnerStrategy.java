/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
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
package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.utils.Optionals;
import java.util.List;
import java.util.Optional;

/**
 * Strategy for detecting token owners of Type nodes and their children.
 *
 * <p>This is the most complex strategy because types appear in many contexts:
 * <ul>
 *   <li>Variable declarations (local, field)</li>
 *   <li>Method return types</li>
 *   <li>Parameters</li>
 *   <li>Extends/implements clauses</li>
 *   <li>Cast expressions</li>
 *   <li>Instanceof expressions</li>
 *   <li>Type parameters and bounds</li>
 * </ul>
 *
 * <p>This strategy is critical for fixing Issue #3365 where nested generic types
 * (e.g., {@code Set<Pair<String, String>>}) were not properly updated by the LPP.
 */
class TypeOwnerStrategy implements TokenOwnerDetector.DetectionStrategy {

    @Override
    public Optional<Node> detect(Node node) {
        // Check if this strategy applies
        Type type = findTypeNode(node);
        if (type == null) {
            return Optional.empty();
        }

        // Find the owner
        Node owner = findTypeOwner(type);
        return Optional.ofNullable(owner);
    }

    /**
     * Finds the Type node for the given node.
     * Returns the node itself if it's a Type, or searches ancestors.
     *
     * @param node the node to analyze
     * @return the Type node, or null if not found or not in a type context
     */
    private Type findTypeNode(Node node) {
        if (node instanceof Type) {
            return (Type) node;
        }

        // Search ancestors, but stop at boundaries
        Node current = node;
        while (current != null) {
            if (current instanceof Type) {
                return (Type) current;
            }

            // Stop at boundaries that indicate we're not in a type context
            if (current instanceof BodyDeclaration || current instanceof ExpressionStmt) {
                return null;
            }

            current = current.getParentNode().orElse(null);
        }

        return null;
    }

    /**
     * Finds the declaration that owns the tokens for the given type.
     *
     * <p>Algorithm: Walk up the AST from the type, checking each parent
     * against known contexts where types appear. Return the first matching
     * declaration.
     *
     * @param type the type node (never null)
     * @return the token owner, or the type itself if no owner found
     */
    private Node findTypeOwner(Type type) {
        Node current = type;

        while (current != null) {
            Node parent = current.getParentNode().orElse(null);
            if (parent == null) {
                break;
            }

            final Node currentNode = current;
            // Check each context using Optional chaining for clean code
            Optional<Node> owner = Optionals.or(
                    () -> checkVariableContext(parent, currentNode),
                    () -> checkParameterContext(parent, currentNode),
                    () -> checkMethodContext(parent, currentNode),
                    () -> checkClassContext(parent, currentNode),
                    () -> checkExpressionContext(parent, currentNode),
                    () -> checkStatementContext(parent, currentNode));

            if (owner.isPresent()) {
                return owner.get();
            }

            current = parent;
        }

        // Fallback: type owns its own tokens
        return type;
    }

    // ========================================================================
    // CONTEXT CHECKERS
    // Each method checks if the parent is a specific context that owns tokens
    // ========================================================================

    /**
     * Checks variable declaration contexts: local variables, fields, enum constants.
     *
     * @param parent the potential owner
     * @param current the current node in the walk
     * @return the owner if this context applies
     */
    private Optional<Node> checkVariableContext(Node parent, Node current) {
        // Local variable declaration
        if (parent instanceof VariableDeclarationExpr) {
            return Optional.of(parent);
        }

        // Field declaration
        if (parent instanceof FieldDeclaration) {
            return Optional.of(parent);
        }

        // Enum constant declaration
        if (parent instanceof EnumConstantDeclaration) {
            return Optional.of(parent);
        }

        return Optional.empty();
    }

    /**
     * Checks parameter contexts: method parameters, receiver parameters.
     *
     * @param parent the potential owner
     * @param current the current node in the walk
     * @return the owner if this context applies
     */
    private Optional<Node> checkParameterContext(Node parent, Node current) {
        // Method/constructor parameter
        if (parent instanceof Parameter) {
            return Optional.of(parent);
        }

        // Receiver parameter (e.g., void method(MyClass MyClass.this))
        if (parent instanceof ReceiverParameter) {
            return Optional.of(parent);
        }

        return Optional.empty();
    }

    /**
     * Checks method/constructor contexts: return types, constructor declarations.
     *
     * @param parent the potential owner
     * @param current the current node in the walk
     * @return the owner if this context applies
     */
    private Optional<Node> checkMethodContext(Node parent, Node current) {
        // Method return type
        if (parent instanceof MethodDeclaration) {
            MethodDeclaration method = (MethodDeclaration) parent;
            // Verify that current is actually the return type (not a parameter type)
            if (current.equals(method.getType()) || isAncestorOf(method.getType(), current)) {
                return Optional.of(parent);
            }
        }

        // Annotation member declaration
        if (parent instanceof AnnotationMemberDeclaration) {
            AnnotationMemberDeclaration member = (AnnotationMemberDeclaration) parent;
            if (current.equals(member.getType()) || isAncestorOf(member.getType(), current)) {
                return Optional.of(parent);
            }
        }

        // Constructor declaration
        if (parent instanceof ConstructorDeclaration) {
            return Optional.of(parent);
        }

        return Optional.empty();
    }

    /**
     * Checks class/interface contexts: extends, implements, permits clauses.
     *
     * @param parent the potential owner
     * @param current the current node in the walk
     * @return the owner if this context applies
     */
    private Optional<Node> checkClassContext(Node parent, Node current) {
        // Class or interface declaration
        if (parent instanceof ClassOrInterfaceDeclaration) {
            ClassOrInterfaceDeclaration classDecl = (ClassOrInterfaceDeclaration) parent;

            // Check extends clause
            if (isInTypeList(classDecl.getExtendedTypes(), current)) {
                return Optional.of(parent);
            }

            // Check implements clause
            if (isInTypeList(classDecl.getImplementedTypes(), current)) {
                return Optional.of(parent);
            }

            // Check permits clause (sealed classes - Java 17+)
            if (isInTypeList(classDecl.getPermittedTypes(), current)) {
                return Optional.of(parent);
            }
        }

        // Record declaration (Java 14+)
        if (parent instanceof RecordDeclaration) {
            RecordDeclaration recordDecl = (RecordDeclaration) parent;

            // Check implements clause
            if (isInTypeList(recordDecl.getImplementedTypes(), current)) {
                return Optional.of(parent);
            }
        }

        // Enum declaration
        if (parent instanceof EnumDeclaration) {
            EnumDeclaration enumDecl = (EnumDeclaration) parent;

            // Check implements clause
            if (isInTypeList(enumDecl.getImplementedTypes(), current)) {
                return Optional.of(parent);
            }
        }

        return Optional.empty();
    }

    /**
     * Checks expression contexts: cast, instanceof, record pattern.
     *
     * @param parent the potential owner
     * @param current the current node in the walk
     * @return the owner if this context applies
     */
    private Optional<Node> checkExpressionContext(Node parent, Node current) {
        // Cast expression: (String) obj
        if (parent instanceof CastExpr) {
            CastExpr cast = (CastExpr) parent;
            // Verify current is the cast type
            if (current.equals(cast.getType()) || isAncestorOf(cast.getType(), current)) {
                // The cast expression itself owns the type tokens
                return Optional.of(parent);
            }
        }

        // Instanceof expression: obj instanceof String
        if (parent instanceof InstanceOfExpr) {
            InstanceOfExpr instanceOf = (InstanceOfExpr) parent;
            // Verify current is the type being checked
            if (current.equals(instanceOf.getType()) || isAncestorOf(instanceOf.getType(), current)) {
                // The instanceof expression owns the type tokens
                return Optional.of(parent);
            }
        }

        // Record pattern expression
        if (parent instanceof RecordPatternExpr) {
            RecordPatternExpr pattern = (RecordPatternExpr) parent;
            if (current.equals(pattern.getType()) || isAncestorOf(pattern.getType(), current)) {
                return Optional.of(parent);
            }
        }

        return Optional.empty();
    }

    /**
     * Checks statement contexts: explicit constructor invocations.
     *
     * @param parent the potential owner
     * @param current the current node in the walk
     * @return the owner if this context applies
     */
    private Optional<Node> checkStatementContext(Node parent, Node current) {
        // Explicit constructor invocation: this(...), super(...)
        if (parent instanceof ExplicitConstructorInvocationStmt) {
            return Optional.of(parent);
        }

        return Optional.empty();
    }

    // ========================================================================
    // UTILITY METHODS
    // ========================================================================

    /**
     * Checks if a node is contained in a list of types (extends, implements, permits).
     *
     * @param types the list of types to check
     * @param node the node to search for
     * @return true if node is in the list or is a descendant of a type in the list
     */
    private boolean isInTypeList(List<? extends Type> types, Node node) {
        for (Type type : types) {
            if (type.equals(node) || isAncestorOf(type, node)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Checks if potentialAncestor is actually an ancestor of node.
     *
     * @param potentialAncestor the potential ancestor
     * @param node the node to check
     * @return true if potentialAncestor is an ancestor of node
     */
    private boolean isAncestorOf(Node potentialAncestor, Node node) {
        Node current = node.getParentNode().orElse(null);

        while (current != null) {
            if (current.equals(potentialAncestor)) {
                return true;
            }
            current = current.getParentNode().orElse(null);
        }

        return false;
    }
}
