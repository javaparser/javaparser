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
import com.github.javaparser.metamodel.JmlMultiExprClauseMetaModel;
import com.github.javaparser.metamodel.OptionalProperty;
import java.util.Objects;
import java.util.Optional;
import java.util.function.Consumer;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * @author Alexander Weigl
 * @version 1 (25.02.22)
 */
public class JmlMultiExprClause extends JmlClause {

    private JmlClauseKind kind;

    @OptionalProperty
    private NodeList<SimpleName> heaps;

    private NodeList<Expression> expressions;

    @AllFieldsConstructor
    public JmlMultiExprClause(
            JmlClauseKind kind, SimpleName name, NodeList<SimpleName> heaps, NodeList<Expression> expressions) {
        this(null, kind, name, heaps, expressions);
    }

    public JmlMultiExprClause(
            TokenRange range,
            JavaToken begin,
            SimpleName label,
            NodeList<SimpleName> heaps,
            NodeList<Expression> exprs) {
        this(range, JmlClauseKind.getKindByToken(begin), label, heaps, exprs);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlClauseKind getKind() {
        return kind;
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
    public NodeList<Expression> getExpressions() {
        return expressions;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlMultiExprClause setExpressions(final NodeList<Expression> expressions) {
        assertNotNull(expressions);
        if (expressions == this.expressions) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.EXPRESSIONS, this.expressions, expressions);
        if (this.expressions != null) this.expressions.setParentNode(null);
        this.expressions = expressions;
        setAsParentNodeOf(expressions);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<NodeList<SimpleName>> getHeaps() {
        return Optional.ofNullable(heaps);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlMultiExprClause setHeaps(final NodeList<SimpleName> heaps) {
        if (heaps == this.heaps) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.HEAPS, this.heaps, heaps);
        if (this.heaps != null) this.heaps.setParentNode(null);
        this.heaps = heaps;
        setAsParentNodeOf(heaps);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlMultiExprClause setKind(final JmlClauseKind kind) {
        assertNotNull(kind);
        if (kind == this.kind) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.KIND, this.kind, kind);
        this.kind = kind;
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null) {
            return false;
        }
        for (int i = 0; i < expressions.size(); i++) {
            if (expressions.get(i) == node) {
                expressions.remove(i);
                return true;
            }
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
        for (int i = 0; i < expressions.size(); i++) {
            if (expressions.get(i) == node) {
                expressions.set(i, (Expression) replacementNode);
                return true;
            }
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
    public JmlMultiExprClause clone() {
        return (JmlMultiExprClause) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlMultiExprClauseMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlMultiExprClauseMetaModel;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlMultiExprClause(
            TokenRange tokenRange,
            JmlClauseKind kind,
            SimpleName name,
            NodeList<SimpleName> heaps,
            NodeList<Expression> expressions) {
        super(tokenRange, name);
        setKind(kind);
        setHeaps(heaps);
        setExpressions(expressions);
        customInitialization();
    }

    public NodeList<Expression> getExpression() {
        return expressions;
    }

    public JmlMultiExprClause setExpression(final NodeList<Expression> expressions) {
        assertNotNull(expressions);
        if (expressions == this.expressions) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.EXPRESSION, this.expressions, expressions);
        if (this.expressions != null) this.expressions.setParentNode(null);
        this.expressions = expressions;
        setAsParentNodeOf(expressions);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJmlMultiExprClause() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlMultiExprClause asJmlMultiExprClause() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlMultiExprClause> toJmlMultiExprClause() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlMultiExprClause(Consumer<JmlMultiExprClause> action) {
        action.accept(this);
    }

    @NonNull()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Expression> expressions() {
        return Objects.requireNonNull(expressions);
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
