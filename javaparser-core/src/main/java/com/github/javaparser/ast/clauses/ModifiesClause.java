package com.github.javaparser.ast.clauses;

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
import com.github.javaparser.metamodel.ModifiesClauseMetaModel;
import com.github.javaparser.ast.observer.ObservableProperty;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Alexander Weigl
 * @version 1 (2/21/21)
 */
public class ModifiesClause extends JmlClause implements LoopContractable, MethodContractable, BlockContractable {

    private NodeList<SimpleName> heaps;

    private NodeList<Expression> exprs;

    @AllFieldsConstructor
    public ModifiesClause(NodeList<SimpleName> heaps, NodeList<Expression> exprs) {
        this(null);
        setKind(Kind.MODIFIES);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public ModifiesClause(TokenRange tokenRange) {
        super(tokenRange);
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
                exprs.set(i, (Expression) replacementNode);
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
    public ModifiesClause clone() {
        return (ModifiesClause) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public ModifiesClauseMetaModel getMetaModel() {
        return JavaParserMetaModel.modifiesClauseMetaModel;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Expression> getExprs() {
        return exprs;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ModifiesClause setExprs(final NodeList<Expression> exprs) {
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
    public ModifiesClause setHeaps(final NodeList<SimpleName> heaps) {
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

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public ModifiesClause(TokenRange tokenRange, NodeList<SimpleName> heaps, NodeList<Expression> exprs) {
        super(tokenRange);
        setHeaps(heaps);
        setExprs(exprs);
        customInitialization();
    }
}
