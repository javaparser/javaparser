package com.github.javaparser.ast.jml.body;

import com.github.javaparser.JavaToken;
import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.*;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.JmlClassInvariantDeclarationMetaModel;
import com.github.javaparser.metamodel.OptionalProperty;
import java.util.Optional;
import java.util.function.Consumer;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.metamodel.JmlClassExprDeclarationMetaModel;

/**
 * @author Alexander Weigl
 * @version 1 (2/21/21)
 */
public class JmlClassExprDeclaration extends JmlClassLevel<JmlClassExprDeclaration> implements NodeWithModifiers<JmlClassExprDeclaration> {

    @OptionalProperty
    private SimpleName kind;

    private NodeList<Modifier> modifiers;

    private Expression invariant;

    public JmlClassExprDeclaration() {
        super(null);
    }

    @AllFieldsConstructor
    public JmlClassExprDeclaration(NodeList<Modifier> modifiers, SimpleName kind, Expression invariant) {
        this(null, modifiers, kind, invariant);
    }

    public JmlClassExprDeclaration(TokenRange range, JavaToken begin, NodeList<Modifier> modifiers, Expression expr) {
        this(range, modifiers, new SimpleName(new TokenRange(begin, begin), begin.getText()), expr);
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
    public Expression getInvariant() {
        return invariant;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlClassExprDeclaration setInvariant(final Expression invariant) {
        assertNotNull(invariant);
        if (invariant == this.invariant) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.INVARIANT, this.invariant, invariant);
        if (this.invariant != null)
            this.invariant.setParentNode(null);
        this.invariant = invariant;
        setAsParentNodeOf(invariant);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null) {
            return false;
        }
        if (kind != null) {
            if (node == kind) {
                removeKind();
                return true;
            }
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
        if (node == invariant) {
            setInvariant((Expression) replacementNode);
            return true;
        }
        if (kind != null) {
            if (node == kind) {
                setKind((SimpleName) replacementNode);
                return true;
            }
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
    public JmlClassExprDeclaration clone() {
        return (JmlClassExprDeclaration) accept(new CloneVisitor(), null);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlClassExprDeclaration(TokenRange tokenRange, NodeList<Modifier> modifiers, SimpleName kind, Expression invariant) {
        super(tokenRange);
        setModifiers(modifiers);
        setKind(kind);
        setInvariant(invariant);
        customInitialization();
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Modifier> getModifiers() {
        return modifiers;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlClassExprDeclaration setModifiers(final NodeList<Modifier> modifiers) {
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
    public boolean isJmlClassInvariantDeclaration() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlClassExprDeclaration asJmlClassInvariantDeclaration() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlClassExprDeclaration> toJmlClassInvariantDeclaration() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlClassInvariantDeclaration(Consumer<JmlClassExprDeclaration> action) {
        action.accept(this);
    }

    @Override
    public boolean isJmlClassExprDeclaration() {
        return true;
    }

    @Override
    public JmlClassExprDeclaration asJmlClassExprDeclaration() {
        return this;
    }

    @Override
    public Optional<JmlClassExprDeclaration> toJmlClassExprDeclaration() {
        return Optional.of(this);
    }

    public void ifJmlClassExprDeclaration(Consumer<JmlClassExprDeclaration> action) {
        action.accept(this);
    }

    public Optional<SimpleName> getKind() {
        return Optional.ofNullable(kind);
    }

    public JmlClassExprDeclaration setKind(final SimpleName kind) {
        if (kind == this.kind) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.KIND, this.kind, kind);
        if (this.kind != null)
            this.kind.setParentNode(null);
        this.kind = kind;
        setAsParentNodeOf(kind);
        return this;
    }

    public JmlClassExprDeclaration removeKind() {
        return setKind(null);
    }

    @Override
    public JmlClassExprDeclarationMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlClassExprDeclarationMetaModel;
    }
}
