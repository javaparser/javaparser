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

package com.github.javaparser.ast.body;

import static com.github.javaparser.ast.expr.NameExpr.*;
import static com.github.javaparser.utils.Utils.ensureNotNull;

import java.util.ArrayList;
import java.util.EnumSet;
import java.util.List;

import com.github.javaparser.Range;
import com.github.javaparser.ast.ArrayBracketPair;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.AssignExpr;
import com.github.javaparser.ast.expr.AssignExpr.Operator;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.nodeTypes.*;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import static com.github.javaparser.ast.Modifier.PUBLIC;
import static com.github.javaparser.ast.type.VoidType.VOID_TYPE;

/**
 * @author Julio Vilmar Gesser
 */
public final class FieldDeclaration extends BodyDeclaration<FieldDeclaration> implements
        NodeWithJavaDoc<FieldDeclaration>,
        NodeWithElementType<FieldDeclaration>,
        NodeWithModifiers<FieldDeclaration>,
        NodeWithVariables<FieldDeclaration> {

    private EnumSet<Modifier> modifiers = EnumSet.noneOf(Modifier.class);

    private Type elementType;

    private List<VariableDeclarator> variables;

    private List<ArrayBracketPair> arrayBracketPairsAfterElementType;

    public FieldDeclaration() {
    }

    public FieldDeclaration(EnumSet<Modifier> modifiers, Type elementType, VariableDeclarator variable) {
        setModifiers(modifiers);
        setElementType(elementType);
        List<VariableDeclarator> aux = new ArrayList<>();
        aux.add(variable);
        setVariables(aux);
    }

    public FieldDeclaration(EnumSet<Modifier> modifiers, Type elementType, List<VariableDeclarator> variables) {
        setModifiers(modifiers);
        setElementType(elementType);
        setVariables(variables);
    }

    public FieldDeclaration(EnumSet<Modifier> modifiers, List<AnnotationExpr> annotations, Type elementType, List<ArrayBracketPair> arrayBracketPairsAfterElementType,
                            List<VariableDeclarator> variables) {
        super(annotations);
        setModifiers(modifiers);
        setElementType(elementType);
        setVariables(variables);
        setArrayBracketPairsAfterElementType(arrayBracketPairsAfterElementType);
    }

    public FieldDeclaration(Range range, EnumSet<Modifier> modifiers, List<AnnotationExpr> annotations, Type elementType,
                            List<VariableDeclarator> variables, List<ArrayBracketPair> arrayBracketPairsAfterElementType) {
        super(range, annotations);
        setModifiers(modifiers);
        setElementType(elementType);
        setVariables(variables);
        setArrayBracketPairsAfterElementType(arrayBracketPairsAfterElementType);
    }

    /**
     * Creates a {@link FieldDeclaration}.
     *
     * @param modifiers
     *            modifiers
     * @param type
     *            type
     * @param variable
     *            variable declarator
     * @return instance of {@link FieldDeclaration}
     */
    public static FieldDeclaration create(EnumSet<Modifier> modifiers, Type type,
                                                          VariableDeclarator variable) {
        List<VariableDeclarator> variables = new ArrayList<>();
        variables.add(variable);
        return new FieldDeclaration(modifiers, type, variables);
    }

    /**
     * Creates a {@link FieldDeclaration}.
     *
     * @param modifiers
     *            modifiers
     * @param type
     *            type
     * @param name
     *            field name
     * @return instance of {@link FieldDeclaration}
     */
    public static FieldDeclaration create(EnumSet<Modifier> modifiers, Type type, String name) {
        VariableDeclaratorId id = new VariableDeclaratorId(name);
        VariableDeclarator variable = new VariableDeclarator(id);
        return create(modifiers, type, variable);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    /**
     * Return the modifiers of this member declaration.
     * 
     * @see Modifier
     * @return modifiers
     */
    @Override
    public EnumSet<Modifier> getModifiers() {
        return modifiers;
    }

    @Override
    public List<VariableDeclarator> getVariables() {
        variables = ensureNotNull(variables);
        return variables;
    }

    @Override
    public FieldDeclaration setModifiers(EnumSet<Modifier> modifiers) {
        this.modifiers = modifiers;
        return this;
    }

    @Override
    public FieldDeclaration setVariables(List<VariableDeclarator> variables) {
        this.variables = variables;
        setAsParentNodeOf(this.variables);
        return this;
    }

    @Override
    public JavadocComment getJavaDoc() {
        if (getComment() instanceof JavadocComment) {
            return (JavadocComment) getComment();
        }
        return null;
    }

    /**
     * Create a getter for this field, <b>will only work if this field declares only 1 identifier and if this field is
     * already added to a ClassOrInterfaceDeclaration</b>
     * 
     * @return the {@link MethodDeclaration} created
     * @throws IllegalStateException if there is more than 1 variable identifier or if this field isn't attached to a
     *             class or enum
     */
    public MethodDeclaration createGetter() {
        if (getVariables().size() != 1)
            throw new IllegalStateException("You can use this only when the field declares only 1 variable name");
        ClassOrInterfaceDeclaration parentClass = getParentNodeOfType(ClassOrInterfaceDeclaration.class);
        EnumDeclaration parentEnum = getParentNodeOfType(EnumDeclaration.class);
        if ((parentClass == null && parentEnum == null) || (parentClass != null && parentClass.isInterface()))
            throw new IllegalStateException(
                    "You can use this only when the field is attached to a class or an enum");

        VariableDeclarator variable = getVariables().get(0);
        String fieldName = variable.getId().getName();
        String fieldNameUpper = fieldName.toUpperCase().substring(0, 1) + fieldName.substring(1, fieldName.length());
        final MethodDeclaration getter;
        if (parentClass != null)
            getter = parentClass.addMethod("get" + fieldNameUpper, PUBLIC);
        else
            getter = parentEnum.addMethod("get" + fieldNameUpper, PUBLIC);
        getter.setType(variable.getType());
        BlockStmt blockStmt = new BlockStmt();
        getter.setBody(blockStmt);
        blockStmt.addStatement(new ReturnStmt(name(fieldName)));
        return getter;
    }

    /**
     * Create a setter for this field, <b>will only work if this field declares only 1 identifier and if this field is
     * already added to a ClassOrInterfaceDeclaration</b>
     * 
     * @return the {@link MethodDeclaration} created
     * @throws IllegalStateException if there is more than 1 variable identifier or if this field isn't attached to a
     *             class or enum
     */
    public MethodDeclaration createSetter() {
        if (getVariables().size() != 1)
            throw new IllegalStateException("You can use this only when the field declares only 1 variable name");
        ClassOrInterfaceDeclaration parentClass = getParentNodeOfType(ClassOrInterfaceDeclaration.class);
        EnumDeclaration parentEnum = getParentNodeOfType(EnumDeclaration.class);
        if ((parentClass == null && parentEnum == null) || (parentClass != null && parentClass.isInterface()))
            throw new IllegalStateException(
                    "You can use this only when the field is attached to a class or an enum");

        VariableDeclarator variable = getVariables().get(0);
        String fieldName = variable.getId().getName();
        String fieldNameUpper = fieldName.toUpperCase().substring(0, 1) + fieldName.substring(1, fieldName.length());

        final MethodDeclaration setter;
        if (parentClass != null)
            setter = parentClass.addMethod("set" + fieldNameUpper, PUBLIC);
        else
            setter = parentEnum.addMethod("set" + fieldNameUpper, PUBLIC);
        setter.setType(VOID_TYPE);
        setter.getParameters().add(new Parameter(variable.getType(), new VariableDeclaratorId(fieldName)));
        BlockStmt blockStmt2 = new BlockStmt();
        setter.setBody(blockStmt2);
        blockStmt2.addStatement(new AssignExpr(new NameExpr("this." + fieldName), new NameExpr(fieldName), Operator.assign));
        return setter;
    }


    @Override
    public Type getElementType() {
        return elementType;
    }

    @Override
    public FieldDeclaration setElementType(final Type elementType) {
        this.elementType = elementType;
        setAsParentNodeOf(this.elementType);
        return this;
    }

    /**
     * @return the array brackets in this position: <code>class C { int[] abc; }</code>
     */
    public List<ArrayBracketPair> getArrayBracketPairsAfterElementType() {
        arrayBracketPairsAfterElementType = ensureNotNull(arrayBracketPairsAfterElementType);
        return arrayBracketPairsAfterElementType;
    }

    @Override
    public FieldDeclaration setArrayBracketPairsAfterElementType(List<ArrayBracketPair> arrayBracketPairsAfterType) {
        this.arrayBracketPairsAfterElementType = arrayBracketPairsAfterType;
        setAsParentNodeOf(arrayBracketPairsAfterType);
        return this;
    }
}
