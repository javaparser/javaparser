package com.github.javaparser.ast.jml.clauses;

import com.github.javaparser.JavaToken;
import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.jml.locref.LocationSetExpression;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.AssignableClauseMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.observer.ObservableProperty;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.metamodel.JmlClauseHLMetaModel;

/**
 * @author Alexander Weigl
 * @version 1 (2/21/21)
 */
public class JmlClauseHL extends JmlClause implements MethodContractable, BlockContractable, LoopContractable {

    private NodeList<SimpleName> heaps;

    private NodeList<Expression> exprs;

    public JmlClauseHL() {
        this(null, null, null);
    }

    @AllFieldsConstructor
    public JmlClauseHL(NodeList<SimpleName> heaps, JmlClauseKind kind, NodeList<Expression> exprs) {
        this(null, kind, heaps, exprs);
    }

    public JmlClauseHL(TokenRange tokenRange, JavaToken token, NodeList<SimpleName> heaps, NodeList<Expression> exprs) {
        this(tokenRange, (JmlClauseKind) null, heaps, exprs);
        setKindByToken(token);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlClauseHL(TokenRange tokenRange, JmlClauseKind kind, NodeList<SimpleName> heaps, NodeList<Expression> exprs) {
        super(tokenRange);
        setHeaps(heaps);
        setExprs(exprs);
        customInitialization();
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < exprs.size(); i++) {
            if (exprs.get(i) == node) {
                exprs.remove(i);
                return true;
            }
        }
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
        for (int i = 0; i < exprs.size(); i++) {
            if (exprs.get(i) == node) {
                exprs.set(i, (LocationSetExpression) replacementNode);
                return true;
            }
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
    public JmlClauseHL clone() {
        return (JmlClauseHL) accept(new CloneVisitor(), null);
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
    public JmlClauseHL(TokenRange tokenRange) {
        super(tokenRange);
        customInitialization();
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Expression> getExprs() {
        return exprs;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlClauseHL setExprs(final NodeList<Expression> exprs) {
        assertNotNull(exprs);
        if (exprs == this.exprs) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.EXPRS, this.exprs, exprs);
        if (this.exprs != null)
            this.exprs.setParentNode(null);
        this.exprs = exprs;
        setAsParentNodeOf(exprs);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<SimpleName> getHeaps() {
        return heaps;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlClauseHL setHeaps(final NodeList<SimpleName> heaps) {
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
    public JmlClauseHLMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlClauseHLMetaModel;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlClauseHL(TokenRange tokenRange, NodeList<SimpleName> heaps, JmlClauseKind kind, NodeList<Expression> exprs) {
        super(tokenRange, kind);
        setHeaps(heaps);
        setExprs(exprs);
        customInitialization();
    }
}
