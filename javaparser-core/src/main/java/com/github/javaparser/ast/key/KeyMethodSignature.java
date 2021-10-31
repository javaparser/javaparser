package com.github.javaparser.ast.key;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.ast.observer.ObservableProperty;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.KeyMethodSignatureMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Generated;

public class KeyMethodSignature extends Node {

    private Name name;

    private NodeList<Type> paramTypes;

    @AllFieldsConstructor
    public KeyMethodSignature(Name name, NodeList<Type> paramTypes) {
        this(null, name, paramTypes);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public KeyMethodSignature(TokenRange tokenRange, Name name, NodeList<Type> paramTypes) {
        super(tokenRange);
        setName(name);
        setParamTypes(paramTypes);
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
    public Name getName() {
        return name;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public KeyMethodSignature setName(final Name name) {
        assertNotNull(name);
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

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Type> getParamTypes() {
        return paramTypes;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public KeyMethodSignature setParamTypes(final NodeList<Type> paramTypes) {
        assertNotNull(paramTypes);
        if (paramTypes == this.paramTypes) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.PARAM_TYPES, this.paramTypes, paramTypes);
        if (this.paramTypes != null)
            this.paramTypes.setParentNode(null);
        this.paramTypes = paramTypes;
        setAsParentNodeOf(paramTypes);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < paramTypes.size(); i++) {
            if (paramTypes.get(i) == node) {
                paramTypes.remove(i);
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
        if (node == name) {
            setName((Name) replacementNode);
            return true;
        }
        for (int i = 0; i < paramTypes.size(); i++) {
            if (paramTypes.get(i) == node) {
                paramTypes.set(i, (Type) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public KeyMethodSignature clone() {
        return (KeyMethodSignature) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public KeyMethodSignatureMetaModel getMetaModel() {
        return JavaParserMetaModel.keyMethodSignatureMetaModel;
    }
}
