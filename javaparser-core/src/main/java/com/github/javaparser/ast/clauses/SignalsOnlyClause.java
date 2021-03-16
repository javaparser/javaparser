package com.github.javaparser.ast.clauses;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.SignalsOnlyMetaModel;

/**
 * @author Alexander Weigl
 * @version 1 (2/21/21)
 */
public class SignalsOnlyClause extends JmlClause implements MethodContractable, BlockContractable {

    private NodeList<Type> types;

    @AllFieldsConstructor
    public SignalsOnlyClause(NodeList<Type> types) {
        super();
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public SignalsOnlyClause(TokenRange tokenRange, NodeList<Type> types) {
        super(tokenRange);
        customInitialization();
    }

    public SignalsOnlyClause() {
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
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public SignalsOnlyClause clone() {
        return (SignalsOnlyClause) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public SignalsOnlyMetaModel getMetaModel() {
        return JavaParserMetaModel.signalsOnlyMetaModel;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    public SignalsOnlyClause(TokenRange tokenRange) {
        super(tokenRange);
        customInitialization();
    }
}
