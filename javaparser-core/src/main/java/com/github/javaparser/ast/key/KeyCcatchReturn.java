package com.github.javaparser.ast.key;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.KeyCcatchReturnMetaModel;
import com.github.javaparser.metamodel.OptionalProperty;
import java.util.Optional;
import org.jspecify.annotations.Nullable;

public class KeyCcatchReturn extends KeyCcatchBranch {

    @OptionalProperty
    private Parameter parameter;

    @OptionalProperty
    private BlockStmt block;

    @AllFieldsConstructor
    public KeyCcatchReturn(Parameter parameter, BlockStmt block) {
        this(null, parameter, block);
    }

    public KeyCcatchReturn(Parameter parameter) {
        this(null, parameter, null);
    }

    public KeyCcatchReturn(BlockStmt block) {
        this(null, null, block);
    }

    public KeyCcatchReturn(TokenRange range, Parameter parameter) {
        this(range, parameter, null);
    }

    public KeyCcatchReturn(TokenRange range, BlockStmt block) {
        this(range, null, block);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public KeyCcatchReturn(TokenRange tokenRange, Parameter parameter, BlockStmt block) {
        super(tokenRange);
        setParameter(parameter);
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
    public KeyCcatchReturn setBlock(final @Nullable() BlockStmt block) {
        if (block == this.block) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.BLOCK, this.block, block);
        if (this.block != null) this.block.setParentNode(null);
        this.block = block;
        setAsParentNodeOf(block);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<Parameter> getParameter() {
        return Optional.ofNullable(parameter);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public KeyCcatchReturn setParameter(final @Nullable() Parameter parameter) {
        if (parameter == this.parameter) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.PARAMETER, this.parameter, parameter);
        if (this.parameter != null) this.parameter.setParentNode(null);
        this.parameter = parameter;
        setAsParentNodeOf(parameter);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public KeyCcatchReturn removeBlock() {
        return setBlock((BlockStmt) null);
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public KeyCcatchReturn removeParameter() {
        return setParameter((Parameter) null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null) {
            return false;
        }
        if (block != null) {
            if (node == block) {
                removeBlock();
                return true;
            }
        }
        if (parameter != null) {
            if (node == parameter) {
                removeParameter();
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
        if (block != null) {
            if (node == block) {
                setBlock((BlockStmt) replacementNode);
                return true;
            }
        }
        if (parameter != null) {
            if (node == parameter) {
                setParameter((Parameter) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public KeyCcatchReturn clone() {
        return (KeyCcatchReturn) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public KeyCcatchReturnMetaModel getMetaModel() {
        return JavaParserMetaModel.keyCcatchReturnMetaModel;
    }

    @com.github.javaparser.ast.key.IgnoreLexPrinting()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public @Nullable() BlockStmt block() {
        return block;
    }

    @com.github.javaparser.ast.key.IgnoreLexPrinting()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public @Nullable() Parameter parameter() {
        return parameter;
    }
}
