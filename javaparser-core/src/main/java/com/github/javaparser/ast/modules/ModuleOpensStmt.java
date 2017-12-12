package com.github.javaparser.ast.modules;

import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.nodeTypes.NodeWithName;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.ModuleOpensStmtMetaModel;
import java.util.Arrays;
import java.util.List;
import static com.github.javaparser.utils.Utils.assertNotNull;
import javax.annotation.Generated;
import com.github.javaparser.TokenRange;
import java.util.function.Consumer;
import java.util.Optional;

public final class ModuleOpensStmt extends ModuleStmt implements NodeWithName<ModuleOpensStmt> {

    private Name name;

    private NodeList<Name> moduleNames;

    public ModuleOpensStmt() {
        this(null, new Name(), new NodeList<>());
    }

    @AllFieldsConstructor
    public ModuleOpensStmt(Name name, NodeList<Name> moduleNames) {
        this(null, name, moduleNames);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public ModuleOpensStmt(TokenRange tokenRange, Name name, NodeList<Name> moduleNames) {
        super(tokenRange);
        setName(name);
        setModuleNames(moduleNames);
        customInitialization();
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

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
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

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Name getName() {
        return name;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ModuleOpensStmt setName(final Name name) {
        assertNotNull(name);
        if (name == this.name) {
            return (ModuleOpensStmt) this;
        }
        notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        if (this.name != null)
            this.name.setParentNode(null);
        this.name = name;
        setAsParentNodeOf(name);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Name> getModuleNames() {
        return moduleNames;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ModuleOpensStmt setModuleNames(final NodeList<Name> moduleNames) {
        assertNotNull(moduleNames);
        if (moduleNames == this.moduleNames) {
            return (ModuleOpensStmt) this;
        }
        notifyPropertyChange(ObservableProperty.MODULE_NAMES, this.moduleNames, moduleNames);
        if (this.moduleNames != null)
            this.moduleNames.setParentNode(null);
        this.moduleNames = moduleNames;
        setAsParentNodeOf(moduleNames);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public ModuleOpensStmt clone() {
        return (ModuleOpensStmt) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public ModuleOpensStmtMetaModel getMetaModel() {
        return JavaParserMetaModel.moduleOpensStmtMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
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
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isModuleOpensStmt() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ModuleOpensStmt asModuleOpensStmt() {
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifModuleOpensStmt(Consumer<ModuleOpensStmt> action) {
        action.accept(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ModuleOpensStmt> toModuleOpensStmt() {
        return Optional.of(this);
    }
}
