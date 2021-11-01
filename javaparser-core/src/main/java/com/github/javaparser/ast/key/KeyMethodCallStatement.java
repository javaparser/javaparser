package com.github.javaparser.ast.key;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Optional;
import java.util.function.Consumer;
import com.github.javaparser.ast.observer.ObservableProperty;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.KeyMethodCallStatementMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.metamodel.OptionalProperty;

public class KeyMethodCallStatement extends Statement {

    @OptionalProperty
    private Name name;

    private KeyAbstractExecutionContext context;

    private BlockStmt block;

    @AllFieldsConstructor
    public KeyMethodCallStatement(Name name, KeyExecutionContext context, BlockStmt block) {
        this(null, name, context, block);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public KeyMethodCallStatement(TokenRange tokenRange, Name name, KeyAbstractExecutionContext context, BlockStmt block) {
        super(tokenRange);
        setName(name);
        setContext(context);
        setBlock(block);
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
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isKeyMethodCallStatement() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public KeyMethodCallStatement asKeyMethodCallStatement() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<KeyMethodCallStatement> toKeyMethodCallStatement() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifKeyMethodCallStatement(Consumer<KeyMethodCallStatement> action) {
        action.accept(this);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public BlockStmt getBlock() {
        return block;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public KeyMethodCallStatement setBlock(final BlockStmt block) {
        assertNotNull(block);
        if (block == this.block) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.BLOCK, this.block, block);
        if (this.block != null)
            this.block.setParentNode(null);
        this.block = block;
        setAsParentNodeOf(block);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public KeyAbstractExecutionContext getContext() {
        return context;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public KeyMethodCallStatement setContext(final KeyAbstractExecutionContext context) {
        assertNotNull(context);
        if (context == this.context) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.CONTEXT, this.context, context);
        if (this.context != null)
            this.context.setParentNode(null);
        this.context = context;
        setAsParentNodeOf(context);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<Name> getName() {
        return Optional.ofNullable(name);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public KeyMethodCallStatement setName(final Name name) {
        if (name == this.name) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        if (this.name != null)
            this.name.setParentNode(null);
        this.name = name;
        setAsParentNodeOf(name);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        if (name != null) {
            if (node == name) {
                removeName();
                return true;
            }
        }
        return super.remove(node);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        if (node == block) {
            setBlock((BlockStmt) replacementNode);
            return true;
        }
        if (node == context) {
            setContext((KeyAbstractExecutionContext) replacementNode);
            return true;
        }
        if (name != null) {
            if (node == name) {
                setName((Name) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public KeyMethodCallStatement clone() {
        return (KeyMethodCallStatement) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public KeyMethodCallStatementMetaModel getMetaModel() {
        return JavaParserMetaModel.keyMethodCallStatementMetaModel;
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public KeyMethodCallStatement removeName() {
        return setName((Name) null);
    }
}
