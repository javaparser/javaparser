package com.github.javaparser.ast.nodeTypes;

import java.util.EnumSet;
import java.util.List;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.InitializerDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Modifier;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.body.VariableDeclaratorId;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.type.ClassOrInterfaceType;

/**
 * A node having members.
 * 
 * The main reason for this interface is to permit users to manipulate homogeneously all nodes with a getMembers
 * method.
 * 
 * 
 */
public interface NodeWithMembers<T> {
    List<BodyDeclaration<?>> getMembers();

    T setMembers(List<BodyDeclaration<?>> members);

    /**
     * Add a field to this and automatically add the import of the type if needed
     * 
     * @param typeClass the type of the field
     * @param modifiers the modifiers like {@link Modifier#PUBLIC}
     * @param name the name of the field
     * @return the {@link FieldDeclaration} created
     */
    public default FieldDeclaration addField(Class<?> typeClass, EnumSet<Modifier> modifiers, String name) {
        ((Node) this).tryAddImportToParentCompilationUnit(typeClass);
        return addField(typeClass.getSimpleName(), modifiers, name);
    }

    /**
     * Add a field to this
     * 
     * @param type the type of the field
     * @param modifiers the modifiers like {@link Modifier#PUBLIC}
     * @param name the name of the field
     * @return the {@link FieldDeclaration} created
     */
    public default FieldDeclaration addField(String type, EnumSet<Modifier> modifiers, String name) {
        FieldDeclaration fieldDeclaration = new FieldDeclaration();
        fieldDeclaration.getVariables().add(new VariableDeclarator(new VariableDeclaratorId(name)));
        fieldDeclaration.setModifiers(modifiers);
        fieldDeclaration.setType(new ClassOrInterfaceType(type));
        getMembers().add(fieldDeclaration);
        fieldDeclaration.setParentNode((Node) this);
        return fieldDeclaration;
    }

    /**
     * Add a private field to this
     * 
     * @param type the type of the field
     * @param name the name of the field
     * @return the {@link FieldDeclaration} created
     */
    public default FieldDeclaration addPrivateField(Class<?> typeClass, String name) {
        return addField(typeClass, EnumSet.of(Modifier.PRIVATE), name);
    }

    /**
     * Add a private field to this and automatically add the import of the type if
     * needed
     * 
     * @param type the type of the field
     * @param name the name of the field
     * @return the {@link FieldDeclaration} created
     */
    public default FieldDeclaration addPrivateField(String type, String name) {
        return addField(type, EnumSet.of(Modifier.PRIVATE), name);
    }

    /**
     * Add a public field to this
     * 
     * @param type the type of the field
     * @param name the name of the field
     * @return the {@link FieldDeclaration} created
     */
    public default FieldDeclaration addPublicField(Class<?> typeClass, String name) {
        return addField(typeClass, EnumSet.of(Modifier.PUBLIC), name);
    }

    /**
     * Add a public field to this and automatically add the import of the type if
     * needed
     * 
     * @param type the type of the field
     * @param name the name of the field
     * @return the {@link FieldDeclaration} created
     */
    public default FieldDeclaration addPublicField(String type, String name) {
        return addField(type, EnumSet.of(Modifier.PUBLIC), name);
    }

    /**
     * Add a protected field to this
     * 
     * @param type the type of the field
     * @param name the name of the field
     * @return the {@link FieldDeclaration} created
     */
    public default FieldDeclaration addProtectedField(Class<?> typeClass, String name) {
        return addField(typeClass, EnumSet.of(Modifier.PROTECTED), name);
    }

    /**
     * Add a protected field to this and automatically add the import of the type
     * if needed
     * 
     * @param type the type of the field
     * @param name the name of the field
     * @return the {@link FieldDeclaration} created
     */
    public default FieldDeclaration addProtectedField(String type, String name) {
        return addField(type, EnumSet.of(Modifier.PROTECTED), name);
    }

    /**
     * Adds a methods to this
     * 
     * @param methodName the method name
     * @param modifiers the modifiers like {@link Modifier#PUBLIC}
     * @return the {@link MethodDeclaration} created
     */
    public default MethodDeclaration addMethod(String methodName, EnumSet<Modifier> modifiers) {
        MethodDeclaration methodDeclaration = new MethodDeclaration();
        methodDeclaration.setName(methodName);
        methodDeclaration.setModifiers(modifiers);
        getMembers().add(methodDeclaration);
        methodDeclaration.setParentNode((Node) this);
        return methodDeclaration;
    }

    /**
     * Adds a constructor to this
     * 
     * @param methodName the method name
     * @param modifiers the modifiers like {@link Modifier#PUBLIC}
     * @return the {@link MethodDeclaration} created
     */
    public default ConstructorDeclaration addCtor(EnumSet<Modifier> modifiers) {
        ConstructorDeclaration constructorDeclaration = new ConstructorDeclaration();
        constructorDeclaration.setModifiers(modifiers);
        constructorDeclaration.setName(((TypeDeclaration<?>) this).getName());
        getMembers().add(constructorDeclaration);
        constructorDeclaration.setParentNode((Node) this);
        return constructorDeclaration;
    }

    public default BlockStmt addInitializer() {
        BlockStmt block = new BlockStmt();
        InitializerDeclaration initializerDeclaration = new InitializerDeclaration(false, block);
        getMembers().add(initializerDeclaration);
        initializerDeclaration.setParentNode((Node) this);
        return block;
    }

    public default BlockStmt addStaticInitializer() {
        BlockStmt block = new BlockStmt();
        InitializerDeclaration initializerDeclaration = new InitializerDeclaration(true, block);
        getMembers().add(initializerDeclaration);
        initializerDeclaration.setParentNode((Node) this);
        return block;
    }

    // TODO remove methods
}
