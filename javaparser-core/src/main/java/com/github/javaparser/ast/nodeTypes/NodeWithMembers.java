package com.github.javaparser.ast.nodeTypes;

import java.util.List;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.ModifierSet;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.body.VariableDeclaratorId;
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
     * @param modifiers the modifiers like {@link ModifierSet#PUBLIC}
     * @param name the name of the field
     * @return the {@link FieldDeclaration} created
     */
    public default FieldDeclaration addField(Class<?> typeClass, int modifiers, String name) {
        ((Node) this).tryAddImportToParentCompilationUnit(typeClass);
        return addField(typeClass.getSimpleName(), modifiers, name);
    }

    /**
     * Add a field to this
     * 
     * @param type the type of the field
     * @param modifiers the modifiers like {@link ModifierSet#PUBLIC}
     * @param name the name of the field
     * @return the {@link FieldDeclaration} created
     */
    public default FieldDeclaration addField(String type, int modifiers, String name) {
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
        return addField(typeClass, ModifierSet.PRIVATE, name);
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
        return addField(type, ModifierSet.PRIVATE, name);
    }

    /**
     * Add a public field to this
     * 
     * @param type the type of the field
     * @param name the name of the field
     * @return the {@link FieldDeclaration} created
     */
    public default FieldDeclaration addPublicField(Class<?> typeClass, String name) {
        return addField(typeClass, ModifierSet.PUBLIC, name);
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
        return addField(type, ModifierSet.PUBLIC, name);
    }

    /**
     * Add a protected field to this
     * 
     * @param type the type of the field
     * @param name the name of the field
     * @return the {@link FieldDeclaration} created
     */
    public default FieldDeclaration addProtectedField(Class<?> typeClass, String name) {
        return addField(typeClass, ModifierSet.PROTECTED, name);
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
        return addField(type, ModifierSet.PROTECTED, name);
    }

    /**
     * Adds a methods to this
     * 
     * @param methodName the method name
     * @param modifiers the modifiers like {@link ModifierSet#PUBLIC}
     * @return the {@link MethodDeclaration} created
     */
    public default MethodDeclaration addMethod(String methodName, int modifiers) {
        MethodDeclaration methodDeclaration = new MethodDeclaration();
        methodDeclaration.setName(methodName);
        methodDeclaration.setModifiers(modifiers);
        getMembers().add(methodDeclaration);
        methodDeclaration.setParentNode((Node) this);
        return methodDeclaration;
    }

    // TODO ctors
}
