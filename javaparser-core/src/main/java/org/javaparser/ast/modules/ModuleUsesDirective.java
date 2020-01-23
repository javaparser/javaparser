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
package org.javaparser.ast.modules;

import org.javaparser.TokenRange;
import org.javaparser.ast.AllFieldsConstructor;
import org.javaparser.ast.Node;
import org.javaparser.ast.expr.Name;
import org.javaparser.ast.nodeTypes.NodeWithName;
import org.javaparser.ast.observer.ObservableProperty;
import org.javaparser.ast.visitor.CloneVisitor;
import org.javaparser.ast.visitor.GenericVisitor;
import org.javaparser.ast.visitor.VoidVisitor;
import java.util.Optional;
import java.util.function.Consumer;
import static org.javaparser.utils.Utils.assertNotNull;
import org.javaparser.metamodel.ModuleUsesDirectiveMetaModel;
import org.javaparser.metamodel.JavaParserMetaModel;
import org.javaparser.ast.Generated;

/**
 * A uses directive in module-info.java. <code>uses V.W;</code>
 */
public class ModuleUsesDirective extends ModuleDirective implements NodeWithName<ModuleUsesDirective> {

    private Name name;

    public ModuleUsesDirective() {
        this(null, new Name());
    }

    @AllFieldsConstructor
    public ModuleUsesDirective(Name name) {
        this(null, name);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("org.javaparser.generator.core.node.MainConstructorGenerator")
    public ModuleUsesDirective(TokenRange tokenRange, Name name) {
        super(tokenRange);
        setName(name);
        customInitialization();
    }

    @Override
    @Generated("org.javaparser.generator.core.node.AcceptGenerator")
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.AcceptGenerator")
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public ModuleUsesDirective setType(final Name name) {
        assertNotNull(name);
        if (name == this.name) {
            return (ModuleUsesDirective) this;
        }
        notifyPropertyChange(ObservableProperty.TYPE, this.name, name);
        if (this.name != null)
            this.name.setParentNode(null);
        this.name = name;
        setAsParentNodeOf(name);
        return this;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.CloneGenerator")
    public ModuleUsesDirective clone() {
        return (ModuleUsesDirective) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isModuleUsesStmt() {
        return true;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public ModuleUsesDirective asModuleUsesStmt() {
        return this;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifModuleUsesStmt(Consumer<ModuleUsesDirective> action) {
        action.accept(this);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ModuleUsesDirective> toModuleUsesStmt() {
        return Optional.of(this);
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public Name getName() {
        return name;
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public ModuleUsesDirective setName(final Name name) {
        assertNotNull(name);
        if (name == this.name) {
            return (ModuleUsesDirective) this;
        }
        notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        if (this.name != null)
            this.name.setParentNode(null);
        this.name = name;
        setAsParentNodeOf(name);
        return this;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        if (node == name) {
            setName((Name) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isModuleUsesDirective() {
        return true;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public ModuleUsesDirective asModuleUsesDirective() {
        return this;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ModuleUsesDirective> toModuleUsesDirective() {
        return Optional.of(this);
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifModuleUsesDirective(Consumer<ModuleUsesDirective> action) {
        action.accept(this);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.GetMetaModelGenerator")
    public ModuleUsesDirectiveMetaModel getMetaModel() {
        return JavaParserMetaModel.moduleUsesDirectiveMetaModel;
    }
}
