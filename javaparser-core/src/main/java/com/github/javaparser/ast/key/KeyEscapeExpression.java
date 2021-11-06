package com.github.javaparser.ast.key;

import com.github.javaparser.JavaToken;
import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Optional;
import java.util.function.Consumer;
import com.github.javaparser.ast.observer.ObservableProperty;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.KeyEscapeExpressionMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.metamodel.OptionalProperty;

public class KeyEscapeExpression extends Expression {

    private Name callee;

    @OptionalProperty
    private NodeList<Expression> arguments;

    @AllFieldsConstructor
    public KeyEscapeExpression(Name callee, NodeList<Expression> arguments) {
        this.callee = callee;
        this.arguments = arguments;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public KeyEscapeExpression(TokenRange tokenRange, Name callee, NodeList<Expression> arguments) {
        super(tokenRange);
        setCallee(callee);
        setArguments(arguments);
        customInitialization();
    }

    public KeyEscapeExpression(TokenRange range, JavaToken callee, NodeList<Expression> arguments) {
        this(range, new Name(callee.toTokenRange(), null, callee.asString()), arguments);
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
    public boolean isKeyEscapeExpression() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public KeyEscapeExpression asKeyEscapeExpression() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<KeyEscapeExpression> toKeyEscapeExpression() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifKeyEscapeExpression(Consumer<KeyEscapeExpression> action) {
        action.accept(this);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<NodeList<Expression>> getArguments() {
        return Optional.ofNullable(arguments);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public KeyEscapeExpression setArguments(final NodeList<Expression> arguments) {
        if (arguments == this.arguments) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.ARGUMENTS, this.arguments, arguments);
        if (this.arguments != null)
            this.arguments.setParentNode(null);
        this.arguments = arguments;
        setAsParentNodeOf(arguments);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Name getCallee() {
        return callee;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public KeyEscapeExpression setCallee(final Name callee) {
        assertNotNull(callee);
        if (callee == this.callee) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.CALLEE, this.callee, callee);
        if (this.callee != null)
            this.callee.setParentNode(null);
        this.callee = callee;
        setAsParentNodeOf(callee);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        if (arguments != null) {
            for (int i = 0; i < arguments.size(); i++) {
                if (arguments.get(i) == node) {
                    arguments.remove(i);
                    return true;
                }
            }
        }
        return super.remove(node);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        if (arguments != null) {
            for (int i = 0; i < arguments.size(); i++) {
                if (arguments.get(i) == node) {
                    arguments.set(i, (Expression) replacementNode);
                    return true;
                }
            }
        }
        if (node == callee) {
            setCallee((Name) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public KeyEscapeExpression clone() {
        return (KeyEscapeExpression) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public KeyEscapeExpressionMetaModel getMetaModel() {
        return JavaParserMetaModel.keyEscapeExpressionMetaModel;
    }
}
