package com.github.javaparser.ast.jml.expr;

import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Jmlish;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.jml.JmlKeyword;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Optional;
import java.util.function.Consumer;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.JmlLabelMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.observer.ObservableProperty;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Alexander Weigl
 * @version 1 (2/21/21)
 */
public class JmlLabel extends Expression implements Jmlish {

    private Kind kind;

    private SimpleName label;

    private Expression expression;

    @AllFieldsConstructor
    public JmlLabel(final Kind kind, SimpleName label, final Expression expression) {
        // TODO
        this(null);
    }

    public enum Kind implements JmlKeyword {

        NONE("\\lbl"), POSITIVE("\\lblpos"), NEGATIVE("\\lblneg");

        private final String symbol;

        Kind(String symbol) {
            this.symbol = symbol;
        }

        @Override
        public String jmlSymbol() {
            return symbol;
        }
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
    public boolean hasParentNode() {
        return false;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJmlLabel() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlLabel asJmlLabel() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlLabel> toJmlLabel() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlLabel(Consumer<JmlLabel> action) {
        action.accept(this);
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
        if (node == expression) {
            setExpression((Expression) replacementNode);
            return true;
        }
        if (node == label) {
            setLabel((SimpleName) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlLabel clone() {
        return (JmlLabel) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlLabelMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlLabelMetaModel;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlLabel(TokenRange tokenRange) {
        super(tokenRange);
        customInitialization();
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Expression getExpression() {
        return expression;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlLabel setExpression(final Expression expression) {
        assertNotNull(expression);
        if (expression == this.expression) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.EXPRESSION, this.expression, expression);
        if (this.expression != null)
            this.expression.setParentNode(null);
        this.expression = expression;
        setAsParentNodeOf(expression);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Kind getKind() {
        return kind;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlLabel setKind(final Kind kind) {
        assertNotNull(kind);
        if (kind == this.kind) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.KIND, this.kind, kind);
        this.kind = kind;
        return this;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    public JmlLabel(TokenRange tokenRange, Kind kind, Expression expression) {
        super(tokenRange);
        setKind(kind);
        setExpression(expression);
        customInitialization();
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public SimpleName getLabel() {
        return label;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlLabel setLabel(final SimpleName label) {
        assertNotNull(label);
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

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlLabel(TokenRange tokenRange, Kind kind, SimpleName label, Expression expression) {
        super(tokenRange);
        setKind(kind);
        setLabel(label);
        setExpression(expression);
        customInitialization();
    }
}
