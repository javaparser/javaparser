package com.github.javaparser.ast.jml.clauses;

import static com.github.javaparser.utils.Utils.assertNotNull;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.JmlMethodSignatureMetaModel;
import com.github.javaparser.metamodel.OptionalProperty;
import java.util.Objects;
import java.util.Optional;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * @author Alexander Weigl
 * @version 1 (02.05.24)
 */
public class JmlMethodSignature extends Node {

    @OptionalProperty
    private Type receiver;

    private SimpleName name;

    private NodeList<Type> argumentTypes = new NodeList<>();

    @AllFieldsConstructor
    private JmlMethodSignature(@Nullable Type receiver, SimpleName name, NodeList<Type> argumentTypes) {
        super(null);
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
    public NodeList<Type> getArgumentTypes() {
        return argumentTypes;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlMethodSignature setArgumentTypes(final NodeList<Type> argumentTypes) {
        assertNotNull(argumentTypes);
        if (argumentTypes == this.argumentTypes) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.ARGUMENT_TYPES, this.argumentTypes, argumentTypes);
        if (this.argumentTypes != null) this.argumentTypes.setParentNode(null);
        this.argumentTypes = argumentTypes;
        setAsParentNodeOf(argumentTypes);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public SimpleName getName() {
        return name;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlMethodSignature setName(final SimpleName name) {
        assertNotNull(name);
        if (name == this.name) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        if (this.name != null) this.name.setParentNode(null);
        this.name = name;
        setAsParentNodeOf(name);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<Type> getReceiver() {
        return Optional.ofNullable(receiver);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlMethodSignature setReceiver(final Type receiver) {
        if (receiver == this.receiver) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.RECEIVER, this.receiver, receiver);
        if (this.receiver != null) this.receiver.setParentNode(null);
        this.receiver = receiver;
        setAsParentNodeOf(receiver);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public JmlMethodSignature removeReceiver() {
        return setReceiver((Type) null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null) {
            return false;
        }
        for (int i = 0; i < argumentTypes.size(); i++) {
            if (argumentTypes.get(i) == node) {
                argumentTypes.remove(i);
                return true;
            }
        }
        if (receiver != null) {
            if (node == receiver) {
                removeReceiver();
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
        for (int i = 0; i < argumentTypes.size(); i++) {
            if (argumentTypes.get(i) == node) {
                argumentTypes.set(i, (Type) replacementNode);
                return true;
            }
        }
        if (node == name) {
            setName((SimpleName) replacementNode);
            return true;
        }
        if (receiver != null) {
            if (node == receiver) {
                setReceiver((Type) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlMethodSignature clone() {
        return (JmlMethodSignature) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlMethodSignatureMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlMethodSignatureMetaModel;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlMethodSignature(TokenRange tokenRange, Type receiver, SimpleName name, NodeList<Type> argumentTypes) {
        super(tokenRange);
        setReceiver(receiver);
        setName(name);
        setArgumentTypes(argumentTypes);
        customInitialization();
    }

    @NonNull()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Type> argumentTypes() {
        return Objects.requireNonNull(argumentTypes);
    }

    @NonNull()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public SimpleName name() {
        return Objects.requireNonNull(name);
    }

    @Nullable()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Type receiver() {
        return receiver;
    }
}
