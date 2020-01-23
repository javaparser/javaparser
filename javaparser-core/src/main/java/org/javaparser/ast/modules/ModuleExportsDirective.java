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

import org.javaparser.ast.AllFieldsConstructor;
import org.javaparser.ast.Node;
import org.javaparser.ast.NodeList;
import org.javaparser.ast.expr.Name;
import org.javaparser.ast.nodeTypes.NodeWithName;
import org.javaparser.ast.observer.ObservableProperty;
import org.javaparser.ast.visitor.CloneVisitor;
import org.javaparser.ast.visitor.GenericVisitor;
import org.javaparser.ast.visitor.VoidVisitor;
import static org.javaparser.StaticJavaParser.parseName;
import static org.javaparser.utils.Utils.assertNotNull;
import org.javaparser.TokenRange;
import java.util.function.Consumer;
import java.util.Optional;
import org.javaparser.metamodel.ModuleExportsDirectiveMetaModel;
import org.javaparser.metamodel.JavaParserMetaModel;
import org.javaparser.ast.Generated;

/**
 * An exports directive in module-info.java. <code>exports R.S to T1.U1, T2.U2;</code>
 */
public class ModuleExportsDirective extends ModuleDirective implements NodeWithName<ModuleExportsDirective> {

    private Name name;

    private NodeList<Name> moduleNames;

    public ModuleExportsDirective() {
        this(null, new Name(), new NodeList<>());
    }

    @AllFieldsConstructor
    public ModuleExportsDirective(Name name, NodeList<Name> moduleNames) {
        this(null, name, moduleNames);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("org.javaparser.generator.core.node.MainConstructorGenerator")
    public ModuleExportsDirective(TokenRange tokenRange, Name name, NodeList<Name> moduleNames) {
        super(tokenRange);
        setName(name);
        setModuleNames(moduleNames);
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
        for (int i = 0; i < moduleNames.size(); i++) {
            if (moduleNames.get(i) == node) {
                moduleNames.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public Name getName() {
        return name;
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public ModuleExportsDirective setName(final Name name) {
        assertNotNull(name);
        if (name == this.name) {
            return (ModuleExportsDirective) this;
        }
        notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        if (this.name != null)
            this.name.setParentNode(null);
        this.name = name;
        setAsParentNodeOf(name);
        return this;
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Name> getModuleNames() {
        return moduleNames;
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public ModuleExportsDirective setModuleNames(final NodeList<Name> moduleNames) {
        assertNotNull(moduleNames);
        if (moduleNames == this.moduleNames) {
            return (ModuleExportsDirective) this;
        }
        notifyPropertyChange(ObservableProperty.MODULE_NAMES, this.moduleNames, moduleNames);
        if (this.moduleNames != null)
            this.moduleNames.setParentNode(null);
        this.moduleNames = moduleNames;
        setAsParentNodeOf(moduleNames);
        return this;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.CloneGenerator")
    public ModuleExportsDirective clone() {
        return (ModuleExportsDirective) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        for (int i = 0; i < moduleNames.size(); i++) {
            if (moduleNames.get(i) == node) {
                moduleNames.set(i, (Name) replacementNode);
                return true;
            }
        }
        if (node == name) {
            setName((Name) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isModuleExportsStmt() {
        return true;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public ModuleExportsDirective asModuleExportsStmt() {
        return this;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifModuleExportsStmt(Consumer<ModuleExportsDirective> action) {
        action.accept(this);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ModuleExportsDirective> toModuleExportsStmt() {
        return Optional.of(this);
    }

    public ModuleExportsDirective addModuleName(String name) {
        moduleNames.add(parseName(name));
        return this;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isModuleExportsDirective() {
        return true;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public ModuleExportsDirective asModuleExportsDirective() {
        return this;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ModuleExportsDirective> toModuleExportsDirective() {
        return Optional.of(this);
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifModuleExportsDirective(Consumer<ModuleExportsDirective> action) {
        action.accept(this);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.GetMetaModelGenerator")
    public ModuleExportsDirectiveMetaModel getMetaModel() {
        return JavaParserMetaModel.moduleExportsDirectiveMetaModel;
    }
}
