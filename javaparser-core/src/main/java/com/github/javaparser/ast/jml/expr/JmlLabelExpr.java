package com.github.javaparser.ast.jml.expr;

import com.github.javaparser.JavaToken;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Jmlish;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.jml.JmlKeyword;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Arrays;
import java.util.Objects;
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
import com.github.javaparser.metamodel.JmlLabelExprMetaModel;

/**
 * @author Alexander Weigl
 * @version 1 (2/21/21)
 */
public class JmlLabelExpr extends Expression implements Jmlish {

    private Kind kind;

    private SimpleName label;

    private Expression expression;

    @AllFieldsConstructor
    public JmlLabelExpr(final Kind kind, SimpleName label, final Expression expression) {
        this(null, kind, label, expression);
    }

    public JmlLabelExpr(TokenRange range, JavaToken quant, SimpleName name, Expression expr) {
        this(range, token2Kind(quant), name, expr);
    }

    private static Kind token2Kind(JavaToken token) {
        return Arrays.stream(Kind.values()).filter(it -> it.jmlSymbol().equals(token.getText())).findFirst().get();
    }

    public enum Kind implements JmlKeyword {

        NEUTRAL("\\lbl"), POSITIVE("\\lblpos"), NEGATIVE("\\lblneg");

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
    public JmlLabelExpr asJmlLabel() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlLabelExpr> toJmlLabel() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlLabel(Consumer<JmlLabelExpr> action) {
        action.accept(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null) {
            return false;
        }
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
    public JmlLabelExpr clone() {
        return (JmlLabelExpr) accept(new CloneVisitor(), null);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlLabelExpr(TokenRange tokenRange) {
        super(tokenRange);
        customInitialization();
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Expression getExpression() {
        return expression;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlLabelExpr setExpression(final Expression expression) {
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
    public JmlLabelExpr setKind(final Kind kind) {
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
    public JmlLabelExpr(TokenRange tokenRange, Kind kind, Expression expression) {
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
    public JmlLabelExpr setLabel(final SimpleName label) {
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
    public JmlLabelExpr(TokenRange tokenRange, Kind kind, SimpleName label, Expression expression) {
        super(tokenRange);
        setKind(kind);
        setLabel(label);
        setExpression(expression);
        customInitialization();
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJmlLabelExpr() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlLabelExpr asJmlLabelExpr() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlLabelExpr> toJmlLabelExpr() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlLabelExpr(Consumer<JmlLabelExpr> action) {
        action.accept(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlLabelExprMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlLabelExprMetaModel;
    }
}
