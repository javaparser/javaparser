package com.github.javaparser.ast.key;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.ast.observer.ObservableProperty;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.KeyExecutionContextMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Generated;

public class KeyExecutionContext extends Node {

    private Type context;

    private KeyMethodSignature signature;

    private Expression instance;

    @AllFieldsConstructor
    public KeyExecutionContext(Type context, KeyMethodSignature signature, Expression instance) {
        this(null, context, signature, instance);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public KeyExecutionContext(TokenRange tokenRange, Type context, KeyMethodSignature signature, Expression instance) {
        super(tokenRange);
        setContext(context);
        setSignature(signature);
        setInstance(instance);
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
    public Type getContext() {
        return context;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public KeyExecutionContext setContext(final Type context) {
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
    public Expression getInstance() {
        return instance;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public KeyExecutionContext setInstance(final Expression instance) {
        assertNotNull(instance);
        if (instance == this.instance) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.INSTANCE, this.instance, instance);
        if (this.instance != null)
            this.instance.setParentNode(null);
        this.instance = instance;
        setAsParentNodeOf(instance);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public KeyMethodSignature getSignature() {
        return signature;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public KeyExecutionContext setSignature(final KeyMethodSignature signature) {
        assertNotNull(signature);
        if (signature == this.signature) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.SIGNATURE, this.signature, signature);
        if (this.signature != null)
            this.signature.setParentNode(null);
        this.signature = signature;
        setAsParentNodeOf(signature);
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
        if (node == context) {
            setContext((Type) replacementNode);
            return true;
        }
        if (node == instance) {
            setInstance((Expression) replacementNode);
            return true;
        }
        if (node == signature) {
            setSignature((KeyMethodSignature) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public KeyExecutionContext clone() {
        return (KeyExecutionContext) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public KeyExecutionContextMetaModel getMetaModel() {
        return JavaParserMetaModel.keyExecutionContextMetaModel;
    }
}
