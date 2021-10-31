package com.github.javaparser.ast.key;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.expr.Expression;
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
import com.github.javaparser.metamodel.KeyLoopScopeBlockMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Generated;

public class KeyLoopScopeBlock extends Statement {

    private Expression indexPV;

    private BlockStmt block;

    @AllFieldsConstructor
    public KeyLoopScopeBlock(Expression indexPV, BlockStmt block) {
        this.indexPV = indexPV;
        this.block = block;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public KeyLoopScopeBlock(TokenRange tokenRange, Expression indexPV, BlockStmt block) {
        super(tokenRange);
        setIndexPV(indexPV);
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
    public boolean isKeyLoopScopeBlock() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public KeyLoopScopeBlock asKeyLoopScopeBlock() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<KeyLoopScopeBlock> toKeyLoopScopeBlock() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifKeyLoopScopeBlock(Consumer<KeyLoopScopeBlock> action) {
        action.accept(this);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public BlockStmt getBlock() {
        return block;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public KeyLoopScopeBlock setBlock(final BlockStmt block) {
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
    public Expression getIndexPV() {
        return indexPV;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public KeyLoopScopeBlock setIndexPV(final Expression indexPV) {
        assertNotNull(indexPV);
        if (indexPV == this.indexPV) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.INDEX_P_V, this.indexPV, indexPV);
        if (this.indexPV != null)
            this.indexPV.setParentNode(null);
        this.indexPV = indexPV;
        setAsParentNodeOf(indexPV);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
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
        if (node == indexPV) {
            setIndexPV((Expression) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public KeyLoopScopeBlock clone() {
        return (KeyLoopScopeBlock) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public KeyLoopScopeBlockMetaModel getMetaModel() {
        return JavaParserMetaModel.keyLoopScopeBlockMetaModel;
    }
}
