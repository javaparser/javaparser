package com.github.javaparser.ast.jml.clauses;

import com.github.javaparser.JavaToken;
import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.RequiresClauseMetaModel;
import com.github.javaparser.ast.observer.ObservableProperty;
import static com.github.javaparser.utils.Utils.assertNotNull;

import com.github.javaparser.metamodel.JmlClauseHEMetaModel;

/**
 * @author Alexander Weigl
 * @version 1 (2/21/21)
 */
public class JmlClauseHE extends JmlClause implements MethodContractable, BlockContractable {

    private NodeList<SimpleName> heaps;

    private Expression expression;

    @AllFieldsConstructor
    public JmlClauseHE(JmlClauseKind kind, NodeList<SimpleName> heaps, Expression expression) {
        this(null, kind, heaps, expression);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlClauseHE(TokenRange tokenRange, JmlClauseKind kind, NodeList<SimpleName> heaps, Expression expression) {
        super(tokenRange, kind);
        setHeaps(heaps);
        setExpression(expression);
        customInitialization();
    }

    public JmlClauseHE() {
    }

    public JmlClauseHE(TokenRange range, JavaToken begin, NodeList<SimpleName> heaps, Expression expression) {
        this(range, JmlClauseKind.NONE, heaps, expression);
        setKindByToken(begin);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < heaps.size(); i++) {
            if (heaps.get(i) == node) {
                heaps.remove(i);
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
        if (node == expression) {
            setExpression((Expression) replacementNode);
            return true;
        }
        for (int i = 0; i < heaps.size(); i++) {
            if (heaps.get(i) == node) {
                heaps.set(i, (SimpleName) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlClauseHE clone() {
        return (JmlClauseHE) accept(new CloneVisitor(), null);
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
    public JmlClauseHE(TokenRange tokenRange) {
        super(tokenRange);
        customInitialization();
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Expression getExpression() {
        return expression;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlClauseHE setExpression(final Expression expression) {
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
    public NodeList<SimpleName> getHeaps() {
        return heaps;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlClauseHE setHeaps(final NodeList<SimpleName> heaps) {
        assertNotNull(heaps);
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
    public JmlClauseHEMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlClauseHEMetaModel;
    }
}
