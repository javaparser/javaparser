package com.github.javaparser.ast.key.sv;

import com.github.javaparser.JavaToken;
import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.resolution.types.ResolvedType;
import java.util.Optional;
import java.util.function.Consumer;
import com.github.javaparser.ast.observer.ObservableProperty;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.KeyMetaConstructTypeMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Generated;

public class KeyMetaConstructType extends Type {

    private Expression expr;

    private String kind;

    public KeyMetaConstructType(TokenRange range) {
        this(range, null, null, null);
    }

    @AllFieldsConstructor
    public KeyMetaConstructType(NodeList<AnnotationExpr> annotations, String kind, Expression expr) {
        this(null, annotations, kind, expr);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public KeyMetaConstructType(TokenRange tokenRange, NodeList<AnnotationExpr> annotations, String kind, Expression expr) {
        super(tokenRange, annotations);
        setKind(kind);
        setExpr(expr);
        customInitialization();
    }

    @Override
    public String asString() {
        return null;
    }

    @Override
    public ResolvedType resolve() {
        return null;
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
    public boolean isKeyMetaConstructType() {
        return true;
    }

    @Override
    public KeyMetaConstructType asKeyMetaConstructType() {
        return this;
    }

    @Override
    public Optional<KeyMetaConstructType> toKeyMetaConstructType() {
        return Optional.of(this);
    }

    public void ifKeyMetaConstructType(Consumer<KeyMetaConstructType> action) {
        action.accept(this);
    }

    public Expression getExpr() {
        return expr;
    }

    public KeyMetaConstructType setExpr(final Expression expr) {
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

    public String getKind() {
        return kind;
    }

    public KeyMetaConstructType setKind(final String kind) {
        assertNotNull(kind);
        if (kind == this.kind) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.KIND, this.kind, kind);
        this.kind = kind;
        return this;
    }

    @Override
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Override
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        if (node == expr) {
            setExpr((Expression) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    public KeyMetaConstructType clone() {
        return (KeyMetaConstructType) accept(new CloneVisitor(), null);
    }

    @Override
    public KeyMetaConstructTypeMetaModel getMetaModel() {
        return JavaParserMetaModel.keyMetaConstructTypeMetaModel;
    }
}
