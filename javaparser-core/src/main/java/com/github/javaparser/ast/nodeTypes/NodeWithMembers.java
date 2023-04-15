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
package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.type.VoidType;
import java.util.List;
import java.util.Optional;
import static com.github.javaparser.StaticJavaParser.parseType;
import static com.github.javaparser.ast.Modifier.Keyword;
import static com.github.javaparser.ast.Modifier.Keyword.*;
import static com.github.javaparser.ast.Modifier.createModifierList;
import static java.util.Collections.unmodifiableList;
import static java.util.stream.Collectors.toList;

/**
 * A node having members.
 * <p>
 * The main reason for this interface is to permit users to manipulate homogeneously all nodes with a getMembers
 * method.
 */
public interface NodeWithMembers<N extends Node> extends NodeWithSimpleName<N> {

    /**
     * @return all members inside the braces of this node,
     * like fields, methods, nested types, etc.
     */
    NodeList<BodyDeclaration<?>> getMembers();

    void tryAddImportToParentCompilationUnit(Class<?> clazz);

    default BodyDeclaration<?> getMember(int i) {
        return getMembers().get(i);
    }

    @SuppressWarnings("unchecked")
    default N setMember(int i, BodyDeclaration<?> member) {
        getMembers().set(i, member);
        return (N) this;
    }

    @SuppressWarnings("unchecked")
    default N addMember(BodyDeclaration<?> member) {
        getMembers().add(member);
        return (N) this;
    }

    N setMembers(NodeList<BodyDeclaration<?>> members);

    /**
     * Add a field to this and automatically add the import of the type if needed
     *
     * @param typeClass the type of the field
     * @param name      the name of the field
     * @param modifiers the modifiers like {@link Modifier.Keyword#PUBLIC}
     * @return the {@link FieldDeclaration} created
     */
    default FieldDeclaration addField(Class<?> typeClass, String name, Modifier.Keyword... modifiers) {
        tryAddImportToParentCompilationUnit(typeClass);
        return addField(typeClass.getSimpleName(), name, modifiers);
    }

    /**
     * Add a field to this.
     *
     * @param type      the type of the field
     * @param name      the name of the field
     * @param modifiers the modifiers like {@link Modifier.Keyword#PUBLIC}
     * @return the {@link FieldDeclaration} created
     */
    default FieldDeclaration addField(String type, String name, Modifier.Keyword... modifiers) {
        return addField(parseType(type), name, modifiers);
    }

    /**
     * Add a field to this.
     *
     * @param type      the type of the field
     * @param name      the name of the field
     * @param modifiers the modifiers like {@link Modifier.Keyword#PUBLIC}
     * @return the {@link FieldDeclaration} created
     */
    default FieldDeclaration addField(Type type, String name, Modifier.Keyword... modifiers) {
        FieldDeclaration fieldDeclaration = new FieldDeclaration();
        VariableDeclarator variable = new VariableDeclarator(type, name);
        fieldDeclaration.getVariables().add(variable);
        fieldDeclaration.setModifiers(createModifierList(modifiers));
        getMembers().add(fieldDeclaration);
        return fieldDeclaration;
    }

    /**
     * Add a field to this and automatically add the import of the type if needed
     *
     * @param typeClass   the type of the field
     * @param name        the name of the field
     * @param initializer the initializer of the field
     * @param modifiers   the modifiers like {@link Modifier.Keyword#PUBLIC}
     * @return the {@link FieldDeclaration} created
     */
    default FieldDeclaration addFieldWithInitializer(Class<?> typeClass, String name, Expression initializer, Modifier.Keyword... modifiers) {
        tryAddImportToParentCompilationUnit(typeClass);
        return addFieldWithInitializer(typeClass.getSimpleName(), name, initializer, modifiers);
    }

    /**
     * Add a field to this.
     *
     * @param type        the type of the field
     * @param name        the name of the field
     * @param initializer the initializer of the field
     * @param modifiers   the modifiers like {@link Modifier.Keyword#PUBLIC}
     * @return the {@link FieldDeclaration} created
     */
    default FieldDeclaration addFieldWithInitializer(String type, String name, Expression initializer, Modifier.Keyword... modifiers) {
        return addFieldWithInitializer(parseType(type), name, initializer, modifiers);
    }

    /**
     * Add a field to this.
     *
     * @param type        the type of the field
     * @param name        the name of the field
     * @param initializer the initializer of the field
     * @param modifiers   the modifiers like {@link Modifier.Keyword#PUBLIC}
     * @return the {@link FieldDeclaration} created
     */
    default FieldDeclaration addFieldWithInitializer(Type type, String name, Expression initializer, Modifier.Keyword... modifiers) {
        FieldDeclaration declaration = addField(type, name, modifiers);
        declaration.getVariables().iterator().next().setInitializer(initializer);
        return declaration;
    }

    /**
     * Add a private field to this.
     *
     * @param typeClass the type of the field
     * @param name      the name of the field
     * @return the {@link FieldDeclaration} created
     */
    default FieldDeclaration addPrivateField(Class<?> typeClass, String name) {
        return addField(typeClass, name, PRIVATE);
    }

    /**
     * Add a private field to this and automatically add the import of the type if
     * needed.
     *
     * @param type the type of the field
     * @param name the name of the field
     * @return the {@link FieldDeclaration} created
     */
    default FieldDeclaration addPrivateField(String type, String name) {
        return addField(type, name, PRIVATE);
    }

    /**
     * Add a private field to this.
     *
     * @param type the type of the field
     * @param name the name of the field
     * @return the {@link FieldDeclaration} created
     */
    default FieldDeclaration addPrivateField(Type type, String name) {
        return addField(type, name, PRIVATE);
    }

    /**
     * Add a public field to this.
     *
     * @param typeClass the type of the field
     * @param name      the name of the field
     * @return the {@link FieldDeclaration} created
     */
    default FieldDeclaration addPublicField(Class<?> typeClass, String name) {
        return addField(typeClass, name, PUBLIC);
    }

    /**
     * Add a public field to this and automatically add the import of the type if
     * needed.
     *
     * @param type the type of the field
     * @param name the name of the field
     * @return the {@link FieldDeclaration} created
     */
    default FieldDeclaration addPublicField(String type, String name) {
        return addField(type, name, PUBLIC);
    }

    /**
     * Add a public field to this.
     *
     * @param type the type of the field
     * @param name the name of the field
     * @return the {@link FieldDeclaration} created
     */
    default FieldDeclaration addPublicField(Type type, String name) {
        return addField(type, name, PUBLIC);
    }

    /**
     * Add a protected field to this.
     *
     * @param typeClass the type of the field
     * @param name      the name of the field
     * @return the {@link FieldDeclaration} created
     */
    default FieldDeclaration addProtectedField(Class<?> typeClass, String name) {
        return addField(typeClass, name, PROTECTED);
    }

    /**
     * Add a protected field to this and automatically add the import of the type
     * if needed.
     *
     * @param type the type of the field
     * @param name the name of the field
     * @return the {@link FieldDeclaration} created
     */
    default FieldDeclaration addProtectedField(String type, String name) {
        return addField(type, name, PROTECTED);
    }

    /**
     * Add a protected field to this.
     *
     * @param type the type of the field
     * @param name the name of the field
     * @return the {@link FieldDeclaration} created
     */
    default FieldDeclaration addProtectedField(Type type, String name) {
        return addField(type, name, PROTECTED);
    }

    /**
     * Adds a methods with void return by default to this.
     *
     * @param methodName the method name
     * @param modifiers  the modifiers like {@link Modifier.Keyword#PUBLIC}
     * @return the {@link MethodDeclaration} created
     */
    default MethodDeclaration addMethod(String methodName, Keyword... modifiers) {
        MethodDeclaration methodDeclaration = new MethodDeclaration();
        methodDeclaration.setName(methodName);
        methodDeclaration.setType(new VoidType());
        methodDeclaration.setModifiers(createModifierList(modifiers));
        getMembers().add(methodDeclaration);
        return methodDeclaration;
    }

    /**
     * Adds a constructor to this node with members.
     *
     * @param modifiers the modifiers like {@link Modifier.Keyword#PUBLIC}
     * @return the created constructor
     */
    default ConstructorDeclaration addConstructor(Modifier.Keyword... modifiers) {
        ConstructorDeclaration constructorDeclaration = new ConstructorDeclaration();
        constructorDeclaration.setModifiers(createModifierList(modifiers));
        constructorDeclaration.setName(getName());
        getMembers().add(constructorDeclaration);
        return constructorDeclaration;
    }

    /**
     * Add an initializer block ({@link InitializerDeclaration}) to this.
     */
    default BlockStmt addInitializer() {
        BlockStmt block = new BlockStmt();
        InitializerDeclaration initializerDeclaration = new InitializerDeclaration(false, block);
        getMembers().add(initializerDeclaration);
        return block;
    }

    /**
     * Add a static initializer block ({@link InitializerDeclaration}) to this.
     */
    default BlockStmt addStaticInitializer() {
        BlockStmt block = new BlockStmt();
        InitializerDeclaration initializerDeclaration = new InitializerDeclaration(true, block);
        getMembers().add(initializerDeclaration);
        return block;
    }

    /**
     * Try to find a {@link MethodDeclaration} by its name
     *
     * @param name the name of the method
     * @return the methods found (multiple in case of overloading)
     */
    default List<MethodDeclaration> getMethodsByName(String name) {
        return unmodifiableList(getMethods().stream().filter(m -> m.getNameAsString().equals(name)).collect(toList()));
    }

    /**
     * Find all methods in the members of this node.
     *
     * @return the methods found. This list is immutable.
     */
    default List<MethodDeclaration> getMethods() {
        return unmodifiableList(getMembers().stream().filter(m -> m instanceof MethodDeclaration).map(m -> (MethodDeclaration) m).collect(toList()));
    }

    /**
     * Try to find a {@link MethodDeclaration} by its parameter types. The given parameter types must <i>literally</i>
     * match the declared types of this node's parameters, so passing the string {@code "List"} to this method will find
     * all methods that have exactly one parameter whose type is declared as {@code List}, but not methods with exactly
     * one parameter whose type is declared as {@code java.util.List} or {@code java.awt.List}. Conversely, passing the
     * string {@code "java.util.List"} to this method will find all methods that have exactly one parameter whose type
     * is declared as {@code java.util.List}, but not if the parameter type is declared as {@code List}. Similarly,
     * note that generics are matched as well: If there is a method that has a parameter declared as
     * {@code List&lt;String&gt;}, then it will be considered as a match only if the given string is
     * {@code "List&lt;String&gt;"}, but not if the given string is only {@code "List"}.
     *
     * @param paramTypes the types of parameters like {@code "Map&lt;Integer, String&gt;", "int"} to match
     *                   {@code void foo(Map&lt;Integer,String&gt; myMap, int number)}
     * @return the methods found
     */
    default List<MethodDeclaration> getMethodsByParameterTypes(String... paramTypes) {
        return unmodifiableList(getMethods().stream().filter(m -> m.hasParametersOfType(paramTypes)).collect(toList()));
    }

    /**
     * Try to find {@link MethodDeclaration}s by their name and parameter types. Parameter types are matched exactly as
     * in the case of {@link #getMethodsByParameterTypes(String...)}.
     *
     * @param paramTypes the types of parameters like {@code "Map&lt;Integer, String&gt;", "int"} to match
     *                   {@code void foo(Map&lt;Integer,String&gt; myMap, int number)}
     * @return the methods found
     */
    default List<MethodDeclaration> getMethodsBySignature(String name, String... paramTypes) {
        return unmodifiableList(getMethodsByName(name).stream().filter(m -> m.hasParametersOfType(paramTypes)).collect(toList()));
    }

    /**
     * Try to find a {@link MethodDeclaration} by its parameter types. Note that this is a match in SimpleName, so
     * {@code java.awt.List} and {@code java.util.List} are identical to this algorithm. In addition, note that it is
     * the erasure of each type which is considered, so passing {@code List.class} to this method will return all
     * methods that have exactly one parameter whose type is named {@code List}, regardless of whether the parameter
     * type is declared without generics as {@code List}, or with generics as {@code List&lt;String&gt;}, or
     * {@code List&lt;Integer&gt;}, etc.
     *
     * @param paramTypes the types of parameters like {@code Map.class, int.class} to match
     *                   {@code void foo(Map&lt;Integer,String&gt; myMap, int number)}
     * @return the methods found
     */
    default List<MethodDeclaration> getMethodsByParameterTypes(Class<?>... paramTypes) {
        return unmodifiableList(getMethods().stream().filter(m -> m.hasParametersOfType(paramTypes)).collect(toList()));
    }

    /**
     * Find all constructors in the members of this node.
     * Note that only "normal" constructors, not the "compact" constructors", within {@link RecordDeclaration}
     * are included in the output of this method.
     *
     * @return the constructors found. This list is immutable.
     */
    default List<ConstructorDeclaration> getConstructors() {
        return unmodifiableList(getMembers().stream().filter(m -> m instanceof ConstructorDeclaration).map(m -> (ConstructorDeclaration) m).collect(toList()));
    }

    /**
     * Try to find a {@link ConstructorDeclaration} with no parameters.
     *
     * @return the constructor found, if any.
     */
    default Optional<ConstructorDeclaration> getDefaultConstructor() {
        return getMembers().stream().filter(m -> m instanceof ConstructorDeclaration).map(m -> (ConstructorDeclaration) m).filter(cd -> cd.getParameters().isEmpty()).findFirst();
    }

    /**
     * Try to find a {@link ConstructorDeclaration} by its parameter types. The given parameter types must
     * <i>literally</i> match the declared types of the desired constructor, so passing the string {@code "List"} to
     * this method will search for a constructor that has exactly one parameter whose type is declared as {@code List},
     * but not for a constructor with exactly one parameter whose type is declared as {@code java.util.List} or
     * {@code java.awt.List}. Conversely, passing the string {@code "java.util.List"} to this method will search for a
     * constructor that has exactly one parameter whose type is declared as {@code java.util.List}, but not for a
     * constructor whose type is declared as {@code List}. Similarly, note that generics are matched as well: If there
     * is a constructor that has a parameter declared as {@code List&lt;String&gt;}, then it will be considered as a
     * match only if the given string is {@code "List&lt;String&gt;"}, but not if the given string is only
     * {@code "List"}.
     *
     * @param paramTypes the types of parameters like {@code "Map&lt;Integer, String&gt;", "int"} to match
     *                   {@code Foo(Map&lt;Integer,String&gt; myMap, int number)}
     * @return the constructor found, if any.
     */
    default Optional<ConstructorDeclaration> getConstructorByParameterTypes(String... paramTypes) {
        return getConstructors().stream().filter(m -> m.hasParametersOfType(paramTypes)).findFirst();
    }

    /**
     * Try to find a {@link ConstructorDeclaration} by its parameter types.  Note that this is a match in SimpleName,
     * so {@code java.awt.List} and {@code java.util.List} are identical to this algorithm. In addition, note that it is
     * the erasure of each type which is considered, so passing {@code List.class} to this method will search for a
     * constructor that has exactly one parameter whose type is named {@code List}, regardless of whether the parameter
     * type is declared without generics as {@code List}, or with generics as {@code List&lt;String&gt;}, or
     * {@code List&lt;Integer&gt;}, etc.
     *
     * @param paramTypes the types of parameters like {@code Map.class, int.class} to match
     *                   {@code Foo(Map&lt;Integer,String&gt; myMap, int number)}
     * @return the constructor found, if any.
     */
    default Optional<ConstructorDeclaration> getConstructorByParameterTypes(Class<?>... paramTypes) {
        return getConstructors().stream().filter(m -> m.hasParametersOfType(paramTypes)).findFirst();
    }

    /**
     * Try to find a {@link FieldDeclaration} by its name
     *
     * @param name the name of the field
     * @return null if not found, the FieldDeclaration otherwise
     */
    default Optional<FieldDeclaration> getFieldByName(String name) {
        return getMembers().stream().filter(m -> m instanceof FieldDeclaration).map(f -> (FieldDeclaration) f).filter(f -> f.getVariables().stream().anyMatch(var -> var.getNameAsString().equals(name))).findFirst();
    }

    /**
     * Find all fields in the members of this node.
     *
     * @return the fields found. This list is immutable.
     */
    default List<FieldDeclaration> getFields() {
        return unmodifiableList(getMembers().stream().filter(m -> m instanceof FieldDeclaration).map(m -> (FieldDeclaration) m).collect(toList()));
    }

    /**
     * @return true if there are no members contained in this node.
     */
    default boolean isEmpty() {
        return getMembers().isEmpty();
    }
}
