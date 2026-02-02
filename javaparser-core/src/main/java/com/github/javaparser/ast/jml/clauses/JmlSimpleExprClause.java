package com.github.javaparser.ast.jml.clauses;

import static com.github.javaparser.utils.Utils.assertNotNull;

import com.github.javaparser.JavaToken;
import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.JmlSimpleExprClauseMetaModel;
import com.github.javaparser.metamodel.OptionalProperty;
import java.util.Objects;
import java.util.Optional;
import java.util.function.Consumer;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * @author Alexander Weigl
 * @version 1 (2/21/21)
 */
public class JmlSimpleExprClause extends JmlClause implements MethodContractable, BlockContractable {

    private JmlClauseKind kind;

    @OptionalProperty
    private NodeList<SimpleName> heaps;

    private Expression expression;

    public JmlSimpleExprClause() {}

    @AllFieldsConstructor
    public JmlSimpleExprClause(JmlClauseKind kind, SimpleName name, NodeList<SimpleName> heaps, Expression expression) {
        this(null, kind, name, heaps, expression);
    }

    public JmlSimpleExprClause(TokenRange range, JavaToken kind, NodeList<SimpleName> heaps, Expression expression) {
        this(range, JmlClauseKind.getKindByToken(kind), null, heaps, expression);
    }

    public JmlSimpleExprClause(TokenRange range, JavaToken kind, Expression expr) {
        this(range, kind, (SimpleName) null, expr);
    }

    public JmlSimpleExprClause(TokenRange range, JavaToken kind, SimpleName name, Expression expr) {
        this(range, JmlClauseKind.getKindByToken(kind), name, null, expr);
    }

    public JmlSimpleExprClause(
            TokenRange range, JavaToken kind, SimpleName name, NodeList<SimpleName> heaps, Expression expr) {
        this(range, JmlClauseKind.getKindByToken(kind), name, heaps, expr);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null) {
            return false;
        }
        if (heaps != null) {
            for (int i = 0; i < heaps.size(); i++) {
                if (heaps.get(i) == node) {
                    heaps.remove(i);
                    return true;
                }
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
        if (node == expression) {
            setExpression((Expression) replacementNode);
            return true;
        }
        if (heaps != null) {
            for (int i = 0; i < heaps.size(); i++) {
                if (heaps.get(i) == node) {
                    heaps.set(i, (SimpleName) replacementNode);
                    return true;
                }
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlSimpleExprClause clone() {
        return (JmlSimpleExprClause) accept(new CloneVisitor(), null);
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

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlSimpleExprClause(TokenRange tokenRange) {
        super(tokenRange);
        customInitialization();
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Expression getExpression() {
        return expression;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlSimpleExprClause setExpression(final NodeList<Expression> expression) {
        assertNotNull(expression);
        notifyPropertyChange(ObservableProperty.EXPRESSION, this.expression, expression);
        if (this.expression != null) this.expression.setParentNode(null);
        setAsParentNodeOf(expression);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<NodeList<SimpleName>> getHeaps() {
        return Optional.ofNullable(heaps);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlSimpleExprClause setHeaps(final NodeList<SimpleName> heaps) {
        if (heaps == this.heaps) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.HEAPS, this.heaps, heaps);
        if (this.heaps != null) this.heaps.setParentNode(null);
        this.heaps = heaps;
        setAsParentNodeOf(heaps);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlClauseKind getKind() {
        return kind;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlSimpleExprClause(
            TokenRange tokenRange,
            JmlClauseKind kind,
            SimpleName name,
            NodeList<SimpleName> heaps,
            Expression expression) {
        super(tokenRange, name);
        setKind(kind);
        setHeaps(heaps);
        setExpression(expression);
        customInitialization();
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlSimpleExprClause setKind(final JmlClauseKind kind) {
        assertNotNull(kind);
        if (kind == this.kind) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.KIND, this.kind, kind);
        this.kind = kind;
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlSimpleExprClause setExpression(final Expression expression) {
        assertNotNull(expression);
        if (expression == this.expression) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.EXPRESSION, this.expression, expression);
        if (this.expression != null) this.expression.setParentNode(null);
        this.expression = expression;
        setAsParentNodeOf(expression);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlSimpleExprClauseMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlSimpleExprClauseMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJmlSimpleExprClause() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlSimpleExprClause asJmlSimpleExprClause() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlSimpleExprClause> toJmlSimpleExprClause() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlSimpleExprClause(Consumer<JmlSimpleExprClause> action) {
        action.accept(this);
    }

    @NonNull()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Expression expression() {
        return Objects.requireNonNull(expression);
    }

    @Nullable()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<SimpleName> heaps() {
        return heaps;
    }

    @NonNull()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlClauseKind kind() {
        return Objects.requireNonNull(kind);
    }
}
