package com.github.javaparser.ast.key;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Optional;
import java.util.function.Consumer;
import com.github.javaparser.ast.observer.ObservableProperty;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.KeyMethodBodyStatementMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.metamodel.OptionalProperty;

public class KeyMethodBodyStatement extends Statement {

    @OptionalProperty
    private Name name;

    private Expression expr;

    private Type source;

    @AllFieldsConstructor
    public KeyMethodBodyStatement(Name name, Expression expr, Type source) {
        this(null, name, expr, source);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public KeyMethodBodyStatement(TokenRange tokenRange, Name name, Expression expr, Type source) {
        super(tokenRange);
        setName(name);
        setExpr(expr);
        setSource(source);
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
    public boolean isKeyMethodBodyStatement() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public KeyMethodBodyStatement asKeyMethodBodyStatement() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<KeyMethodBodyStatement> toKeyMethodBodyStatement() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifKeyMethodBodyStatement(Consumer<KeyMethodBodyStatement> action) {
        action.accept(this);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Expression getExpr() {
        return expr;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public KeyMethodBodyStatement setExpr(final Expression expr) {
        assertNotNull(expr);
        if (expr == this.expr) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.EXPR, this.expr, expr);
        if (this.expr != null)
            this.expr.setParentNode(null);
        this.expr = expr;
        setAsParentNodeOf(expr);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<Name> getName() {
        return Optional.ofNullable(name);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public KeyMethodBodyStatement setName(final Name name) {
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
    public Type getSource() {
        return source;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public KeyMethodBodyStatement setSource(final Type source) {
        assertNotNull(source);
        if (source == this.source) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.SOURCE, this.source, source);
        if (this.source != null)
            this.source.setParentNode(null);
        this.source = source;
        setAsParentNodeOf(source);
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
        if (node == expr) {
            setExpr((Expression) replacementNode);
            return true;
        }
        if (name != null) {
            if (node == name) {
                setName((Name) replacementNode);
                return true;
            }
        }
        if (node == source) {
            setSource((Type) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public KeyMethodBodyStatement clone() {
        return (KeyMethodBodyStatement) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public KeyMethodBodyStatementMetaModel getMetaModel() {
        return JavaParserMetaModel.keyMethodBodyStatementMetaModel;
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public KeyMethodBodyStatement removeName() {
        return setName((Name) null);
    }
}
