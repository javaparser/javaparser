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
package com.github.javaparser.ast.expr;

import com.github.javaparser.Range;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;
import com.github.javaparser.ast.nodeTypes.NodeWithVariables;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Arrays;
import java.util.EnumSet;
import java.util.List;
import java.util.stream.Collectors;
import static com.github.javaparser.ast.NodeList.nodeList;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.VariableDeclarationExprMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

/**
 * A declaration of variables.
 * It is an expression, so it can be put in places like the initializer of a for loop,
 * or the resources part of the try statement.
 * <br/><code>final int x=3, y=55</code>
 *
 * @author Julio Vilmar Gesser
 */
public final class VariableDeclarationExpr extends Expression implements NodeWithModifiers<VariableDeclarationExpr>, NodeWithAnnotations<VariableDeclarationExpr>, NodeWithVariables<VariableDeclarationExpr> {

    private EnumSet<Modifier> modifiers;

    private NodeList<AnnotationExpr> annotations;

    private NodeList<VariableDeclarator> variables;

    public VariableDeclarationExpr() {
        this(null, EnumSet.noneOf(Modifier.class), new NodeList<>(), new NodeList<>());
    }

    public VariableDeclarationExpr(final Type type, String variableName) {
        this(null, EnumSet.noneOf(Modifier.class), new NodeList<>(), nodeList(new VariableDeclarator(type, variableName)));
    }

    public VariableDeclarationExpr(VariableDeclarator var) {
        this(null, EnumSet.noneOf(Modifier.class), new NodeList<>(), nodeList(var));
    }

    public VariableDeclarationExpr(final Type type, String variableName, Modifier... modifiers) {
        this(null, Arrays.stream(modifiers).collect(Collectors.toCollection(() -> EnumSet.noneOf(Modifier.class))), new NodeList<>(), nodeList(new VariableDeclarator(type, variableName)));
    }

    public VariableDeclarationExpr(VariableDeclarator var, Modifier... modifiers) {
        this(null, Arrays.stream(modifiers).collect(Collectors.toCollection(() -> EnumSet.noneOf(Modifier.class))), new NodeList<>(), nodeList(var));
    }

    public VariableDeclarationExpr(final NodeList<VariableDeclarator> variables) {
        this(null, EnumSet.noneOf(Modifier.class), new NodeList<>(), variables);
    }

    public VariableDeclarationExpr(final EnumSet<Modifier> modifiers, final NodeList<VariableDeclarator> variables) {
        this(null, modifiers, new NodeList<>(), variables);
    }

    @AllFieldsConstructor
    public VariableDeclarationExpr(final EnumSet<Modifier> modifiers, final NodeList<AnnotationExpr> annotations, final NodeList<VariableDeclarator> variables) {
        this(null, modifiers, annotations, variables);
    }

    public VariableDeclarationExpr(final Range range, final EnumSet<Modifier> modifiers, final NodeList<AnnotationExpr> annotations, final NodeList<VariableDeclarator> variables) {
        super(range);
        setModifiers(modifiers);
        setAnnotations(annotations);
        setVariables(variables);
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    @Override
    public NodeList<AnnotationExpr> getAnnotations() {
        return annotations;
    }

    /**
     * Return the modifiers of this variable declaration.
     *
     * @return modifiers
     * @see Modifier
     */
    @Override
    public EnumSet<Modifier> getModifiers() {
        return modifiers;
    }

    @Override
    public NodeList<VariableDeclarator> getVariables() {
        return variables;
    }

    @Override
    public VariableDeclarationExpr setAnnotations(final NodeList<AnnotationExpr> annotations) {
        assertNotNull(annotations);
        notifyPropertyChange(ObservableProperty.ANNOTATIONS, this.annotations, annotations);
        if (this.annotations != null)
            this.annotations.setParentNode(null);
        this.annotations = annotations;
        setAsParentNodeOf(annotations);
        return this;
    }

    @Override
    public VariableDeclarationExpr setModifiers(final EnumSet<Modifier> modifiers) {
        assertNotNull(modifiers);
        notifyPropertyChange(ObservableProperty.MODIFIERS, this.modifiers, modifiers);
        this.modifiers = modifiers;
        return this;
    }

    @Override
    public VariableDeclarationExpr setVariables(final NodeList<VariableDeclarator> variables) {
        assertNotNull(variables);
        notifyPropertyChange(ObservableProperty.VARIABLES, this.variables, variables);
        if (this.variables != null)
            this.variables.setParentNode(null);
        this.variables = variables;
        setAsParentNodeOf(variables);
        return this;
    }

    @Override
    public List<NodeList<?>> getNodeLists() {
        return Arrays.asList(getAnnotations(), getVariables());
    }

    @Override
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < annotations.size(); i++) {
            if (annotations.get(i) == node) {
                annotations.remove(i);
                return true;
            }
        }
        for (int i = 0; i < variables.size(); i++) {
            if (variables.get(i) == node) {
                variables.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Override
    public VariableDeclarationExpr clone() {
        return (VariableDeclarationExpr) accept(new CloneVisitor(), null);
    }

    @Override
    public VariableDeclarationExprMetaModel getMetaModel() {
        return JavaParserMetaModel.variableDeclarationExprMetaModel;
    }
}
