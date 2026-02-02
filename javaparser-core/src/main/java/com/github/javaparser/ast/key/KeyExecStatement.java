package com.github.javaparser.ast.key;

import static com.github.javaparser.utils.Utils.assertNotNull;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.KeyExecStatementMetaModel;
import java.util.Objects;
import java.util.Optional;
import java.util.function.Consumer;
import org.jspecify.annotations.NonNull;

public class KeyExecStatement extends Statement {

    private BlockStmt execBlock;

    private NodeList<KeyCcatchBranch> branches;

    @AllFieldsConstructor
    public KeyExecStatement(BlockStmt execBlock, NodeList<KeyCcatchBranch> branches) {
        this(null, execBlock, branches);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public KeyExecStatement(TokenRange tokenRange, BlockStmt execBlock, NodeList<KeyCcatchBranch> branches) {
        super(tokenRange);
        setExecBlock(execBlock);
        setBranches(branches);
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

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<KeyCcatchBranch> getBranches() {
        return branches;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public KeyExecStatement setBranches(final @NonNull() NodeList<KeyCcatchBranch> branches) {
        assertNotNull(branches);
        if (branches == this.branches) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.BRANCHES, this.branches, branches);
        if (this.branches != null) this.branches.setParentNode(null);
        this.branches = branches;
        setAsParentNodeOf(branches);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public BlockStmt getExecBlock() {
        return execBlock;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public KeyExecStatement setExecBlock(final @NonNull() BlockStmt execBlock) {
        assertNotNull(execBlock);
        if (execBlock == this.execBlock) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.EXEC_BLOCK, this.execBlock, execBlock);
        if (this.execBlock != null) this.execBlock.setParentNode(null);
        this.execBlock = execBlock;
        setAsParentNodeOf(execBlock);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null) {
            return false;
        }
        for (int i = 0; i < branches.size(); i++) {
            if (branches.get(i) == node) {
                branches.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null) {
            return false;
        }
        for (int i = 0; i < branches.size(); i++) {
            if (branches.get(i) == node) {
                branches.set(i, (KeyCcatchBranch) replacementNode);
                return true;
            }
        }
        if (node == execBlock) {
            setExecBlock((BlockStmt) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public KeyExecStatement clone() {
        return (KeyExecStatement) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public KeyExecStatementMetaModel getMetaModel() {
        return JavaParserMetaModel.keyExecStatementMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isKeyExecStatement() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public KeyExecStatement asKeyExecStatement() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<KeyExecStatement> toKeyExecStatement() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifKeyExecStatement(Consumer<KeyExecStatement> action) {
        action.accept(this);
    }

    @com.github.javaparser.ast.key.IgnoreLexPrinting()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public @NonNull() NodeList<KeyCcatchBranch> branches() {
        return Objects.requireNonNull(branches);
    }

    @com.github.javaparser.ast.key.IgnoreLexPrinting()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public @NonNull() BlockStmt execBlock() {
        return Objects.requireNonNull(execBlock);
    }
}
