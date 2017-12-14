package com.github.javaparser.ast.modules;

import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.nodeTypes.NodeWithType;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.ModuleProvidesStmtMetaModel;
import java.util.Arrays;
import java.util.List;
import static com.github.javaparser.utils.Utils.assertNotNull;
import javax.annotation.Generated;
import com.github.javaparser.TokenRange;
import java.util.function.Consumer;
import java.util.Optional;

public final class ModuleProvidesStmt extends ModuleStmt implements NodeWithType<ModuleProvidesStmt, Type> {

    private Type type;

    private NodeList<Type> withTypes;

    public ModuleProvidesStmt() {
        this(null, new ClassOrInterfaceType(), new NodeList<>());
    }

    @AllFieldsConstructor
    public ModuleProvidesStmt(Type type, NodeList<Type> withTypes) {
        this(null, type, withTypes);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public ModuleProvidesStmt(TokenRange tokenRange, Type type, NodeList<Type> withTypes) {
        super(tokenRange);
        setType(type);
        setWithTypes(withTypes);
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
        for (int i = 0; i < withTypes.size(); i++) {
            if (withTypes.get(i) == node) {
                withTypes.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Type getType() {
        return type;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ModuleProvidesStmt setType(final Type type) {
        assertNotNull(type);
        if (type == this.type) {
            return (ModuleProvidesStmt) this;
        }
        notifyPropertyChange(ObservableProperty.TYPE, this.type, type);
        if (this.type != null)
            this.type.setParentNode(null);
        this.type = type;
        setAsParentNodeOf(type);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Type> getWithTypes() {
        return withTypes;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ModuleProvidesStmt setWithTypes(final NodeList<Type> withTypes) {
        assertNotNull(withTypes);
        if (withTypes == this.withTypes) {
            return (ModuleProvidesStmt) this;
        }
        notifyPropertyChange(ObservableProperty.WITH_TYPES, this.withTypes, withTypes);
        if (this.withTypes != null)
            this.withTypes.setParentNode(null);
        this.withTypes = withTypes;
        setAsParentNodeOf(withTypes);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public ModuleProvidesStmt clone() {
        return (ModuleProvidesStmt) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public ModuleProvidesStmtMetaModel getMetaModel() {
        return JavaParserMetaModel.moduleProvidesStmtMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        if (node == type) {
            setType((Type) replacementNode);
            return true;
        }
        for (int i = 0; i < withTypes.size(); i++) {
            if (withTypes.get(i) == node) {
                withTypes.set(i, (Type) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isModuleProvidesStmt() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ModuleProvidesStmt asModuleProvidesStmt() {
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifModuleProvidesStmt(Consumer<ModuleProvidesStmt> action) {
        action.accept(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ModuleProvidesStmt> toModuleProvidesStmt() {
        return Optional.of(this);
    }
}
