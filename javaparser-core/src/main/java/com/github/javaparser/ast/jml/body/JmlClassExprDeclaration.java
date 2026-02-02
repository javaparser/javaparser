package com.github.javaparser.ast.jml.body;

import static com.github.javaparser.utils.Utils.assertNotNull;

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
import com.github.javaparser.metamodel.JmlClassExprDeclarationMetaModel;
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
public class JmlClassExprDeclaration extends JmlClassLevelDeclaration<JmlClassExprDeclaration>
        implements NodeWithModifiers<JmlClassExprDeclaration> {

    private SimpleName kind;

    @OptionalProperty
    private SimpleName name;

    private NodeList<Modifier> modifiers;

    private Expression invariant;

    private NodeList<SimpleName> jmlTags;

    public JmlClassExprDeclaration() {
        super(null);
    }

    @AllFieldsConstructor
    public JmlClassExprDeclaration(
            NodeList<SimpleName> jmlTags,
            NodeList<Modifier> modifiers,
            SimpleName kind,
            SimpleName name,
            Expression invariant) {
        this(null, jmlTags, modifiers, kind, name, invariant);
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
        if (this.invariant != null) this.invariant.setParentNode(null);
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
        for (int i = 0; i < jmlTags.size(); i++) {
            if (jmlTags.get(i) == node) {
                jmlTags.remove(i);
                return true;
            }
        }
        for (int i = 0; i < modifiers.size(); i++) {
            if (modifiers.get(i) == node) {
                modifiers.remove(i);
                return true;
            }
        }
        if (name != null) {
            if (node == name) {
                removeName();
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
        for (int i = 0; i < jmlTags.size(); i++) {
            if (jmlTags.get(i) == node) {
                jmlTags.set(i, (SimpleName) replacementNode);
                return true;
            }
        }
        if (node == kind) {
            setKind((SimpleName) replacementNode);
            return true;
        }
        for (int i = 0; i < modifiers.size(); i++) {
            if (modifiers.get(i) == node) {
                modifiers.set(i, (Modifier) replacementNode);
                return true;
            }
        }
        if (name != null) {
            if (node == name) {
                setName((SimpleName) replacementNode);
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
    public JmlClassExprDeclaration(
            TokenRange tokenRange, NodeList<Modifier> modifiers, SimpleName kind, Expression invariant) {
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
        if (this.modifiers != null) this.modifiers.setParentNode(null);
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
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJmlClassExprDeclaration() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlClassExprDeclaration asJmlClassExprDeclaration() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlClassExprDeclaration> toJmlClassExprDeclaration() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlClassExprDeclaration(Consumer<JmlClassExprDeclaration> action) {
        action.accept(this);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public SimpleName getKind() {
        return kind;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlClassExprDeclaration setKind(final SimpleName kind) {
        assertNotNull(kind);
        if (kind == this.kind) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.KIND, this.kind, kind);
        if (this.kind != null) this.kind.setParentNode(null);
        this.kind = kind;
        setAsParentNodeOf(kind);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public JmlClassExprDeclaration removeKind() {
        return setKind(null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlClassExprDeclarationMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlClassExprDeclarationMetaModel;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<SimpleName> getName() {
        return Optional.ofNullable(name);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlClassExprDeclaration setName(final SimpleName name) {
        if (name == this.name) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        if (this.name != null) this.name.setParentNode(null);
        this.name = name;
        setAsParentNodeOf(name);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public JmlClassExprDeclaration removeName() {
        return setName((SimpleName) null);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlClassExprDeclaration(
            TokenRange tokenRange,
            NodeList<SimpleName> jmlTags,
            NodeList<Modifier> modifiers,
            SimpleName kind,
            SimpleName name,
            Expression invariant) {
        super(tokenRange);
        setJmlTags(jmlTags);
        setModifiers(modifiers);
        setKind(kind);
        setName(name);
        setInvariant(invariant);
        customInitialization();
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<SimpleName> getJmlTags() {
        return jmlTags;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlClassExprDeclaration setJmlTags(final NodeList<SimpleName> jmlTags) {
        assertNotNull(jmlTags);
        if (jmlTags == this.jmlTags) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.JML_TAGS, this.jmlTags, jmlTags);
        if (this.jmlTags != null) this.jmlTags.setParentNode(null);
        this.jmlTags = jmlTags;
        setAsParentNodeOf(jmlTags);
        return this;
    }

    @NonNull()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Expression invariant() {
        return Objects.requireNonNull(invariant);
    }

    @NonNull()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<SimpleName> jmlTags() {
        return Objects.requireNonNull(jmlTags);
    }

    @NonNull()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public SimpleName kind() {
        return Objects.requireNonNull(kind);
    }

    @NonNull()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Modifier> modifiers() {
        return Objects.requireNonNull(modifiers);
    }

    @Nullable()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public SimpleName name() {
        return name;
    }
}
