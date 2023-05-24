/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2023 The JavaParser Team.
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
package com.github.javaparser.resolution;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.PatternExpr;
import com.github.javaparser.quality.Nullable;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.model.Value;
import com.github.javaparser.resolution.types.ResolvedType;
import java.util.Collections;
import java.util.List;
import java.util.Optional;

/**
 * Context is very similar to scope.
 * In the context we look for solving symbols.
 *
 * @author Federico Tomassetti
 */
public interface Context {

    /**
     * Returns the node wrapped in the context
     */
    <N extends Node> N getWrappedNode();

    /**
     * @return The parent context, if there is one. For example, a method exists within a compilation unit.
     */
    Optional<Context> getParent();

    /* Type resolution */
    /**
     * Default to no generics available in this context, delegating solving to the parent context.
     * Contexts which have generics available to it will override this method.
     * For example class and method declarations, and method calls.
     *
     * @param name For example, solving {@code T} within {@code class Foo<T> {}} or
     * @return The resolved generic type, if found.
     */
    default Optional<ResolvedType> solveGenericType(String name) {
        // Default to solving within the parent context.
        return solveGenericTypeInParentContext(name);
    }

    default Optional<ResolvedType> solveGenericTypeInParentContext(String name) {
        Optional<Context> optionalParentContext = getParent();
        if (!optionalParentContext.isPresent()) {
            return Optional.empty();
        }
        // Delegate solving to the parent context.
        return optionalParentContext.get().solveGenericType(name);
    }

    /**
     * Default to being unable to solve any reference in this context, delegating solving to the parent context.
     * Contexts which exist as the "parent" of a resolvable type will override this method.
     * For example, a compilation unit can contain classes. A class declaration can also contain types (e.g. a subclass).
     *
     * @param name For example, solving {@code List} or {@code java.util.List}.
     * @return The declaration associated with the given type name.
     *
     * @deprecated Consider using method {@link #solveType(String, List)} that also consider the type arguments.
     *             If you want to keep to use the new function, but keep the same behavior consider passing type
     *             arguments as {@code null}.
     */
    @Deprecated
    default SymbolReference<ResolvedTypeDeclaration> solveType(String name) {
        return solveType(name, null);
    }

    /**
     * Method used to solve a name with an expected list of type arguments.
     * <br>
     * This method differs from {@link Context#solveType(String)} by taking the type arguments in consideration.
     * For example, lets imagine that we have a project containing the following classes:
     * <ul>
     *     <li>com/example/Alpha.java</li>
     *     <li>com/example/Beta.java</li>
     * </ul>
     * Where Alpha creates a inner interface called CustomInterface and Beta implements Alpha.CustomInterface and
     * also declares a inner interface called CustomInterface with type arguments. Using this method we can
     * specify which type arguments we are expecting and will be resolved with the type matching that declaration.
     *
     * @param name          The name to be solved.
     * @param typeArguments The list of expected type arguments.
     *
     * @return The declaration associated with the given type name.
     */
    default SymbolReference<ResolvedTypeDeclaration> solveType(String name, @Nullable List<ResolvedType> typeArguments) {
        // Default to solving within the parent context.
        return solveTypeInParentContext(name, typeArguments);
    }

    /**
     * Solve a name in the parent context.
     *
     * @param name The name to be solved.
     *
     * @return The declaration associated with the given type name.
     *
     * @deprecated Consider using method {@link #solveTypeInParentContext(String, List)} that also consider the type arguments.
     *             If you want to keep to use the new function, but keep the same behavior consider passing type
     *             arguments as {@code null}.
     */
    @Deprecated
    default SymbolReference<ResolvedTypeDeclaration> solveTypeInParentContext(String name) {
        return solveTypeInParentContext(name, null);
    }

    /**
     * Solve a name with type arguments in the parent context.
     *
     * @param name          The name to be solved.
     * @param typeArguments The list of expected type arguments.
     *
     * @return The declaration associated with the given type name.
     */
    default SymbolReference<ResolvedTypeDeclaration> solveTypeInParentContext(String name, @Nullable List<ResolvedType> typeArguments) {
        Optional<Context> optionalParentContext = getParent();
        if (!optionalParentContext.isPresent()) {
            return SymbolReference.unsolved();
        }
        // Delegate solving to the parent context.
        return optionalParentContext.get().solveType(name, typeArguments);
    }

    /* Symbol resolution */
    /**
     * Used where a symbol is being used (e.g. solving {@code x} when used as an argument {@code doubleThis(x)}, or calculation {@code return x * 2;}).
     * @param name the variable / reference / identifier used.
     * @return // FIXME: Better documentation on how this is different to solveSymbolAsValue()
     */
    default SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name) {
        // Default to solving within the parent context.
        return solveSymbolInParentContext(name);
    }

    default SymbolReference<? extends ResolvedValueDeclaration> solveSymbolInParentContext(String name) {
        Optional<Context> optionalParentContext = getParent();
        if (!optionalParentContext.isPresent()) {
            return SymbolReference.unsolved();
        }
        // Delegate solving to the parent context.
        return optionalParentContext.get().solveSymbol(name);
    }

    /**
     * Used where a symbol is being used (e.g. solving {@code x} when used as an argument {@code doubleThis(x)}, or calculation {@code return x * 2;}).
     * @param name the variable / reference / identifier used.
     * @return // FIXME: Better documentation on how this is different to solveSymbol()
     */
    default Optional<Value> solveSymbolAsValue(String name) {
        SymbolReference<? extends ResolvedValueDeclaration> ref = solveSymbol(name);
        if (!ref.isSolved()) {
            return Optional.empty();
        }
        return Optional.of(Value.from(ref.getCorrespondingDeclaration()));
    }

    default Optional<Value> solveSymbolAsValueInParentContext(String name) {
        SymbolReference<? extends ResolvedValueDeclaration> ref = solveSymbolInParentContext(name);
        if (!ref.isSolved()) {
            return Optional.empty();
        }
        return Optional.of(Value.from(ref.getCorrespondingDeclaration()));
    }

    /**
     * The fields that are declared and in this immediate context made visible to a given child.
     * This list could include values which are shadowed.
     */
    default List<ResolvedFieldDeclaration> fieldsExposedToChild(Node child) {
        return Collections.emptyList();
    }

    /**
     * The local variables that are declared in this immediate context and made visible to a given child.
     * This list could include values which are shadowed.
     */
    default List<VariableDeclarator> localVariablesExposedToChild(Node child) {
        return Collections.emptyList();
    }

    /**
     * The parameters that are declared in this immediate context and made visible to a given child.
     * This list could include values which are shadowed.
     */
    default List<Parameter> parametersExposedToChild(Node child) {
        return Collections.emptyList();
    }

    /**
     * The pattern expressions that are declared in this immediate context and made visible to a given child.
     * This list could include values which are shadowed.
     */
    default List<PatternExpr> patternExprsExposedToChild(Node child) {
        return Collections.emptyList();
    }

    /**
     */
    default List<PatternExpr> patternExprsExposedFromChildren() {
        return Collections.emptyList();
    }

    /**
     */
    default List<PatternExpr> negatedPatternExprsExposedFromChildren() {
        return Collections.emptyList();
    }

    /**
     * Aim to resolve the given name by looking for a variable matching it.
     * <p>
     * To do it consider local variables that are visible in a certain scope as defined in JLS 6.3. Scope of a
     * Declaration.
     * <p>
     * 1. The scope of a local variable declaration in a block (§14.4) is the rest of the block in which the
     * declaration
     * appears, starting with its own initializer and including any further declarators to the right in the local
     * variable declaration statement.
     * <p>
     * 2. The scope of a local variable declared in the ForInit part of a basic for statement (§14.14.1) includes all
     * of the following:
     * 2.1 Its own initializer
     * 2.2 Any further declarators to the right in the ForInit part of the for statement
     * 2.3 The Expression and ForUpdate parts of the for statement
     * 2.4 The contained Statement
     * <p>
     * 3. The scope of a local variable declared in the FormalParameter part of an enhanced for statement (§14.14.2) is
     * the contained Statement.
     * 4. The scope of a parameter of an exception handler that is declared in a catch clause of a try statement
     * (§14.20) is the entire block associated with the catch.
     * <p>
     * 5. The scope of a variable declared in the ResourceSpecification of a try-with-resources statement (§14.20.3) is
     * from the declaration rightward over the remainder of the ResourceSpecification and the entire try block
     * associated with the try-with-resources statement.
     */
    default Optional<VariableDeclarator> localVariableDeclarationInScope(String name) {
        if (!getParent().isPresent()) {
            return Optional.empty();
        }
        // First check if the variable is directly declared within this context.
        Node wrappedNode = getWrappedNode();
        Context parentContext = getParent().get();
        Optional<VariableDeclarator> localResolutionResults = parentContext.localVariablesExposedToChild(wrappedNode).stream().filter(vd -> vd.getNameAsString().equals(name)).findFirst();
        if (localResolutionResults.isPresent()) {
            return localResolutionResults;
        }
        // If we don't find the variable locally, escalate up the scope hierarchy to see if it is declared there.
        return parentContext.localVariableDeclarationInScope(name);
    }

    default Optional<Parameter> parameterDeclarationInScope(String name) {
        if (!getParent().isPresent()) {
            return Optional.empty();
        }
        // First check if the parameter is directly declared within this context.
        Node wrappedNode = getWrappedNode();
        Context parentContext = getParent().get();
        Optional<Parameter> localResolutionResults = parentContext.parametersExposedToChild(wrappedNode).stream().filter(vd -> vd.getNameAsString().equals(name)).findFirst();
        if (localResolutionResults.isPresent()) {
            return localResolutionResults;
        }
        // If we don't find the parameter locally, escalate up the scope hierarchy to see if it is declared there.
        return parentContext.parameterDeclarationInScope(name);
    }

    /**
     * With respect to solving, the AST "parent" of a block statement is not necessarily the same as the scope parent.
     * <br>Example:
     * <br>
     * <pre>{@code
     *  public String x() {
     *      if(x) {
     *          // Parent node: the block attached to the method declaration
     *          // Scope-parent: the block attached to the method declaration
     *      } else if {
     *          // Parent node: the if
     *          // Scope-parent: the block attached to the method declaration
     *      } else {
     *          // Parent node: the elseif
     *          // Scope-parent: the block attached to the method declaration
     *      }
     *  }
     * }</pre>
     */
    default Optional<PatternExpr> patternExprInScope(String name) {
        if (!getParent().isPresent()) {
            return Optional.empty();
        }
        Context parentContext = getParent().get();
        // FIXME: "scroll backwards" from the wrapped node
        // FIXME: If there are multiple patterns, throw an error?
        // First check if the pattern is directly declared within this context.
        Node wrappedNode = getWrappedNode();
        Optional<PatternExpr> localResolutionResults = parentContext.patternExprsExposedToChild(wrappedNode).stream().filter(vd -> vd.getNameAsString().equals(name)).findFirst();
        if (localResolutionResults.isPresent()) {
            return localResolutionResults;
        }
        // If we don't find the parameter locally, escalate up the scope hierarchy to see if it is declared there.
        return parentContext.patternExprInScope(name);
    }

    default Optional<ResolvedFieldDeclaration> fieldDeclarationInScope(String name) {
        if (!getParent().isPresent()) {
            return Optional.empty();
        }
        Context parentContext = getParent().get();
        // First check if the parameter is directly declared within this context.
        Node wrappedNode = getWrappedNode();
        Optional<ResolvedFieldDeclaration> localResolutionResults = parentContext.fieldsExposedToChild(wrappedNode).stream().filter(vd -> vd.getName().equals(name)).findFirst();
        if (localResolutionResults.isPresent()) {
            return localResolutionResults;
        }
        // If we don't find the field locally, escalate up the scope hierarchy to see if it is declared there.
        return parentContext.fieldDeclarationInScope(name);
    }

    /* Constructor resolution */
    /**
     * We find the method declaration which is the best match for the given name and list of typeParametersValues.
     */
    default SymbolReference<ResolvedConstructorDeclaration> solveConstructor(List<ResolvedType> argumentsTypes) {
        throw new IllegalArgumentException("Constructor resolution is available only on Class Context");
    }

    /* Methods resolution */
    /**
     * We find the method declaration which is the best match for the given name and list of typeParametersValues.
     */
    default SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> argumentsTypes, boolean staticOnly) {
        // Default to solving within the parent context.
        return solveMethodInParentContext(name, argumentsTypes, staticOnly);
    }

    default SymbolReference<ResolvedMethodDeclaration> solveMethodInParentContext(String name, List<ResolvedType> argumentsTypes, boolean staticOnly) {
        Optional<Context> optionalParentContext = getParent();
        if (!optionalParentContext.isPresent()) {
            return SymbolReference.unsolved();
        }
        // Delegate solving to the parent context.
        return optionalParentContext.get().solveMethod(name, argumentsTypes, staticOnly);
    }

    /**
     * Similar to solveMethod but we return a MethodUsage.
     * A MethodUsage corresponds to a MethodDeclaration plus the resolved type variables.
     */
    Optional<MethodUsage> solveMethodAsUsage(String name, List<ResolvedType> argumentsTypes);
}
