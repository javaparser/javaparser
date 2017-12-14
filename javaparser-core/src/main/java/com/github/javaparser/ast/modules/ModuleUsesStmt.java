package com.github.javaparser.ast.modules;

import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.nodeTypes.NodeWithType;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.ModuleUsesStmtMetaModel;
import static com.github.javaparser.utils.Utils.assertNotNull;
import javax.annotation.Generated;
import com.github.javaparser.TokenRange;
import java.util.function.Consumer;
import java.util.Optional;

public final class ModuleUsesStmt extends ModuleStmt implements NodeWithType<ModuleUsesStmt, Type> {

    private Type type;

    public ModuleUsesStmt() {
        this(null);
    }

    @AllFieldsConstructor
    public ModuleUsesStmt(Type type) {
        this(null, type);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public ModuleUsesStmt(TokenRange tokenRange, Type type) {
        super(tokenRange);
        setType(type);
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
        return super.remove(node);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Type getType() {
        return type;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ModuleUsesStmt setType(final Type type) {
        assertNotNull(type);
        if (type == this.type) {
            return (ModuleUsesStmt) this;
        }
        notifyPropertyChange(ObservableProperty.TYPE, this.type, type);
        if (this.type != null)
            this.type.setParentNode(null);
        this.type = type;
        setAsParentNodeOf(type);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public ModuleUsesStmt clone() {
        return (ModuleUsesStmt) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public ModuleUsesStmtMetaModel getMetaModel() {
        return JavaParserMetaModel.moduleUsesStmtMetaModel;
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
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isModuleUsesStmt() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ModuleUsesStmt asModuleUsesStmt() {
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifModuleUsesStmt(Consumer<ModuleUsesStmt> action) {
        action.accept(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ModuleUsesStmt> toModuleUsesStmt() {
        return Optional.of(this);
    }
}
