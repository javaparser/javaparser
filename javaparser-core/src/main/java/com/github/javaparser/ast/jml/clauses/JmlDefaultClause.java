package com.github.javaparser.ast.jml.clauses;

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
import com.github.javaparser.metamodel.JmlDefaultClauseMetaModel;
import com.github.javaparser.metamodel.OptionalProperty;
import java.util.Optional;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Alexander Weigl
 * @version 1 (2/21/21)
 */
public class JmlDefaultClause extends JmlClause implements MethodContractable, BlockContractable {

    private JmlClauseKind kind;

    @OptionalProperty
    private NodeList<SimpleName> heaps;

    private NodeList<Expression> expression;

    @AllFieldsConstructor
    public JmlDefaultClause(JmlClauseKind kind, SimpleName name, NodeList<SimpleName> heaps, NodeList<Expression> expression) {
        this(null, kind, name, heaps, expression);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlDefaultClause(TokenRange tokenRange, SimpleName name, JmlClauseKind kind, NodeList<SimpleName> heaps, NodeList<Expression> expression) {
        super(tokenRange, name);
        setHeaps(heaps);
        setExpression(expression);
        customInitialization();
    }

    public JmlDefaultClause() {
    }

    public JmlDefaultClause(TokenRange range, JavaToken kind, NodeList<SimpleName> heaps, Expression expression) {
        this(range, JmlClauseKind.getKindByToken(kind), heaps, new NodeList<>(expression));
    }

    public JmlDefaultClause(TokenRange range, JavaToken begin, Expression expr) {
        this(range, begin, null, expr);
    }

    public JmlDefaultClause(TokenRange range, JavaToken kind, NodeList<SimpleName> heaps, NodeList<Expression> exprs) {
        this(range, JmlClauseKind.getKindByToken(kind), heaps, exprs);
    }

    public JmlDefaultClause(TokenRange range, JavaToken begin, NodeList<Expression> exprs) {
        this(range, begin, new NodeList<>(), exprs);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlDefaultClause(TokenRange tokenRange, JmlClauseKind kind, NodeList<SimpleName> heaps, NodeList<Expression> expression) {
        super(tokenRange);
        setHeaps(heaps);
        setExpression(expression);
        customInitialization();
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null) {
            return false;
        }
        for (int i = 0; i < expression.size(); i++) {
            if (expression.get(i) == node) {
                expression.remove(i);
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
        for (int i = 0; i < expression.size(); i++) {
            if (expression.get(i) == node) {
                expression.set(i, (Expression) replacementNode);
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
    public JmlDefaultClause clone() {
        return (JmlDefaultClause) accept(new CloneVisitor(), null);
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
    public JmlDefaultClause(TokenRange tokenRange) {
        super(tokenRange);
        customInitialization();
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Expression> getExpression() {
        return expression;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlDefaultClause setExpression(final NodeList<Expression> expression) {
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
    public Optional<NodeList<SimpleName>> getHeaps() {
        return Optional.ofNullable(heaps);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlDefaultClause setHeaps(final NodeList<SimpleName> heaps) {
        if (heaps == this.heaps) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.HEAPS, this.heaps, heaps);
        if (this.heaps != null)
            this.heaps.setParentNode(null);
        this.heaps = heaps;
        setAsParentNodeOf(heaps);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlDefaultClauseMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlDefaultClauseMetaModel;
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
    public JmlDefaultClause(TokenRange tokenRange, JmlClauseKind kind, SimpleName name, NodeList<SimpleName> heaps, NodeList<Expression> expression) {
        super(tokenRange, name);
        setKind(kind);
        setHeaps(heaps);
        setExpression(expression);
        customInitialization();
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlDefaultClause setKind(final JmlClauseKind kind) {
        assertNotNull(kind);
        if (kind == this.kind) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.KIND, this.kind, kind);
        this.kind = kind;
        return this;
    }
}
