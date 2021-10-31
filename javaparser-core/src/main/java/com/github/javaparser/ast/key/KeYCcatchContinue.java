package com.github.javaparser.ast.key;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.OptionalProperty;
import java.util.Optional;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.KeYCcatchContinueMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Generated;

public class KeYCcatchContinue extends KeYCcatchBranch {

    @OptionalProperty
    private Name label;

    @OptionalProperty
    private BlockStmt block;

    @AllFieldsConstructor
    public KeYCcatchContinue(Name label, BlockStmt block) {
        this(null, label, block);
    }

    public KeYCcatchContinue(TokenRange tokenRange, BlockStmt block) {
        this(tokenRange, (Name) null, block);
    }

    public KeYCcatchContinue(TokenRange tokenRange, Name label) {
        this(tokenRange, label, null);
    }

    public KeYCcatchContinue(TokenRange tokenRange, String s, BlockStmt block) {
        this(tokenRange, new Name(s), block);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public KeYCcatchContinue(TokenRange tokenRange, Name label, BlockStmt block) {
        super(tokenRange);
        setLabel(label);
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

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<BlockStmt> getBlock() {
        return Optional.ofNullable(block);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public KeYCcatchContinue setBlock(final BlockStmt block) {
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
    public Optional<Name> getLabel() {
        return Optional.ofNullable(label);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public KeYCcatchContinue setLabel(final Name label) {
        if (label == this.label) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.LABEL, this.label, label);
        if (this.label != null)
            this.label.setParentNode(null);
        this.label = label;
        setAsParentNodeOf(label);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public KeYCcatchContinue removeBlock() {
        return setBlock((BlockStmt) null);
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public KeYCcatchContinue removeLabel() {
        return setLabel((Name) null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        if (block != null) {
            if (node == block) {
                removeBlock();
                return true;
            }
        }
        if (label != null) {
            if (node == label) {
                removeLabel();
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
        if (block != null) {
            if (node == block) {
                setBlock((BlockStmt) replacementNode);
                return true;
            }
        }
        if (label != null) {
            if (node == label) {
                setLabel((Name) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public KeYCcatchContinue clone() {
        return (KeYCcatchContinue) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public KeYCcatchContinueMetaModel getMetaModel() {
        return JavaParserMetaModel.keYCcatchContinueMetaModel;
    }
}
