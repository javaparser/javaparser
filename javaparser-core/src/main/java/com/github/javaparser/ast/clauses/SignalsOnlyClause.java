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
import com.github.javaparser.ast.observer.ObservableProperty;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.metamodel.SignalsOnlyClauseMetaModel;

/**
 * @author Alexander Weigl
 * @version 1 (2/21/21)
 */
public class SignalsOnlyClause extends JmlClause implements MethodContractable, BlockContractable {

    private NodeList<Type> types;

    @AllFieldsConstructor
    public SignalsOnlyClause(NodeList<Type> types) {
        this(null, null);
        setKind(Kind.DIVERGES);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public SignalsOnlyClause(TokenRange tokenRange, NodeList<Type> types) {
        super(tokenRange);
        setTypes(types);
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
        for (int i = 0; i < types.size(); i++) {
            if (types.get(i) == node) {
                types.remove(i);
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
        for (int i = 0; i < types.size(); i++) {
            if (types.get(i) == node) {
                types.set(i, (Type) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public SignalsOnlyClause clone() {
        return (SignalsOnlyClause) accept(new CloneVisitor(), null);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public SignalsOnlyClause(TokenRange tokenRange) {
        super(tokenRange);
        customInitialization();
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Type> getTypes() {
        return types;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public SignalsOnlyClause setTypes(final NodeList<Type> types) {
        assertNotNull(types);
        if (types == this.types) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.TYPES, this.types, types);
        if (this.types != null)
            this.types.setParentNode(null);
        this.types = types;
        setAsParentNodeOf(types);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public SignalsOnlyClauseMetaModel getMetaModel() {
        return JavaParserMetaModel.signalsOnlyClauseMetaModel;
    }
}
