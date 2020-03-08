/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2020 The JavaParser Team.
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
package com.github.javaparser.ast.modules;

import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.nodeTypes.NodeWithName;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.ModuleDeclarationMetaModel;
import static com.github.javaparser.StaticJavaParser.parseModuleDirective;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.Generated;

/**
 * A Java 9 Jigsaw module declaration. <code>@Foo module com.github.abc { requires a.B; }</code>
 */
public class ModuleDeclaration extends Node implements NodeWithName<ModuleDeclaration>, NodeWithAnnotations<ModuleDeclaration> {

    private Name name;

    private NodeList<AnnotationExpr> annotations;

    private boolean isOpen;

    private NodeList<ModuleDirective> directives;

    public ModuleDeclaration() {
        this(null, new NodeList<>(), new Name(), false, new NodeList<>());
    }

    public ModuleDeclaration(Name name, boolean isOpen) {
        this(null, new NodeList<>(), name, isOpen, new NodeList<>());
    }

    @AllFieldsConstructor
    public ModuleDeclaration(NodeList<AnnotationExpr> annotations, Name name, boolean isOpen, NodeList<ModuleDirective> directives) {
        this(null, annotations, name, isOpen, directives);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public ModuleDeclaration(TokenRange tokenRange, NodeList<AnnotationExpr> annotations, Name name, boolean isOpen, NodeList<ModuleDirective> directives) {
        super(tokenRange);
        this.setAnnotations(annotations);
        this.setName(name);
        this.setOpen(isOpen);
        this.setDirectives(directives);
        this.customInitialization();
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.AcceptGenerator")
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.AcceptGenerator")
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Name getName() {
        return this.name;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ModuleDeclaration setName(final Name name) {
        assertNotNull(name);
        if (name == this.name) {
            return this;
        }
        this.notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        if (this.name != null) {
            this.name.setParentNode(null);
        }
        this.name = name;
        this.setAsParentNodeOf(name);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<AnnotationExpr> getAnnotations() {
        return this.annotations;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ModuleDeclaration setAnnotations(final NodeList<AnnotationExpr> annotations) {
        assertNotNull(annotations);
        if (annotations == this.annotations) {
            return this;
        }
        this.notifyPropertyChange(ObservableProperty.ANNOTATIONS, this.annotations, annotations);
        if (this.annotations != null) {
            this.annotations.setParentNode(null);
        }
        this.annotations = annotations;
        this.setAsParentNodeOf(annotations);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null) {
            return false;
        }
        for (int i = 0; i < this.annotations.size(); i++) {
            if (this.annotations.get(i) == node) {
                this.annotations.remove(i);
                return true;
            }
        }
        for (int i = 0; i < this.directives.size(); i++) {
            if (this.directives.get(i) == node) {
                this.directives.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public boolean isOpen() {
        return this.isOpen;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ModuleDeclaration setOpen(final boolean isOpen) {
        if (isOpen == this.isOpen) {
            return this;
        }
        this.notifyPropertyChange(ObservableProperty.OPEN, this.isOpen, isOpen);
        this.isOpen = isOpen;
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<ModuleDirective> getDirectives() {
        return this.directives;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ModuleDeclaration setDirectives(final NodeList<ModuleDirective> directives) {
        assertNotNull(directives);
        if (directives == this.directives) {
            return this;
        }
        this.notifyPropertyChange(ObservableProperty.DIRECTIVES, this.directives, directives);
        if (this.directives != null) {
            this.directives.setParentNode(null);
        }
        this.directives = directives;
        this.setAsParentNodeOf(directives);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public ModuleDeclaration clone() {
        return (ModuleDeclaration) this.accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public ModuleDeclarationMetaModel getMetaModel() {
        return JavaParserMetaModel.moduleDeclarationMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null) {
            return false;
        }
        for (int i = 0; i < this.annotations.size(); i++) {
            if (this.annotations.get(i) == node) {
                this.annotations.set(i, (AnnotationExpr) replacementNode);
                return true;
            }
        }
        for (int i = 0; i < this.directives.size(); i++) {
            if (this.directives.get(i) == node) {
                this.directives.set(i, (ModuleDirective) replacementNode);
                return true;
            }
        }
        if (node == this.name) {
            this.setName((Name) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    /**
     * Add a directive to the module, like "exports R.S to T1.U1, T2.U2;"
     */
    public ModuleDeclaration addDirective(String directive) {
        return addDirective(parseModuleDirective(directive));
    }

    public ModuleDeclaration addDirective(ModuleDirective directive) {
        getDirectives().add(directive);
        return this;
    }
}
