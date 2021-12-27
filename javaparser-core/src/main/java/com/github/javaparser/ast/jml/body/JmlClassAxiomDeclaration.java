package com.github.javaparser.ast.jml.body;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Optional;
import java.util.function.Consumer;
import com.github.javaparser.ast.observer.ObservableProperty;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.JmlClassAxiomDeclarationMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Generated;

/**
 * @author Alexander Weigl
 * @version 1 (12/13/21)
 */
public class JmlClassAxiomDeclaration extends JmlClassLevel<JmlClassAccessibleDeclaration> implements NodeWithModifiers<JmlClassAxiomDeclaration> {

    NodeList<Modifier> modifiers;

    Expression expr;

    @AllFieldsConstructor
    public JmlClassAxiomDeclaration(NodeList<Modifier> modifiers, Expression expr) {
        this.modifiers = modifiers;
        this.expr = expr;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlClassAxiomDeclaration(TokenRange tokenRange, NodeList<Modifier> modifiers, Expression expr) {
        super(tokenRange);
        setModifiers(modifiers);
        setExpr(expr);
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

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Modifier> getModifiers() {
        return modifiers;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlClassAxiomDeclaration setModifiers(final NodeList<Modifier> modifiers) {
        assertNotNull(modifiers);
        if (modifiers == this.modifiers) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.MODIFIERS, this.modifiers, modifiers);
        if (this.modifiers != null)
            this.modifiers.setParentNode(null);
        this.modifiers = modifiers;
        setAsParentNodeOf(modifiers);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJmlClassAxiomDeclaration() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlClassAxiomDeclaration asJmlClassAxiomDeclaration() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlClassAxiomDeclaration> toJmlClassAxiomDeclaration() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlClassAxiomDeclaration(Consumer<JmlClassAxiomDeclaration> action) {
        action.accept(this);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Expression getExpr() {
        return expr;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlClassAxiomDeclaration setExpr(final Expression expr) {
        assertNotNull(expr);
        if (expr == this.expr) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.EXPR, this.expr, expr);
        if (this.expr != null)
            this.expr.setParentNode(null);
        this.expr = expr;
        setAsParentNodeOf(expr);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null) {
            return false;
        }
        for (int i = 0; i < modifiers.size(); i++) {
            if (modifiers.get(i) == node) {
                modifiers.remove(i);
                return true;
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
        if (node == expr) {
            setExpr((Expression) replacementNode);
            return true;
        }
        for (int i = 0; i < modifiers.size(); i++) {
            if (modifiers.get(i) == node) {
                modifiers.set(i, (Modifier) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlClassAxiomDeclaration clone() {
        return (JmlClassAxiomDeclaration) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlClassAxiomDeclarationMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlClassAxiomDeclarationMetaModel;
    }
}
