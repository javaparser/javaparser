package com.github.javaparser.ast.key.sv;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.resolution.Context;
import com.github.javaparser.resolution.types.ResolvedType;
import java.util.Optional;
import java.util.function.Consumer;
import com.github.javaparser.ast.observer.ObservableProperty;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.KeyTypeSVMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;

public class KeyTypeSV extends Type {

    private String text;

    @AllFieldsConstructor
    public KeyTypeSV(String text) {
        this(null, null, text);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public KeyTypeSV(TokenRange tokenRange, String text) {
        super(tokenRange);
        setText(text);
        customInitialization();
    }

    public KeyTypeSV(TokenRange tokenRange, NodeList<AnnotationExpr> annotations, String text) {
        super(tokenRange, annotations);
        this.text = text;
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

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public String getText() {
        return text;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public KeyTypeSV setText(final String text) {
        assertNotNull(text);
        if (text == this.text) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.TEXT, this.text, text);
        this.text = text;
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public KeyTypeSV clone() {
        return (KeyTypeSV) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public KeyTypeSVMetaModel getMetaModel() {
        return JavaParserMetaModel.keyTypeSVMetaModel;
    }

    @Override
    public ResolvedType convertToUsage(Context context) {
        //TODO weigl
        return null;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isKeyTypeSV() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public KeyTypeSV asKeyTypeSV() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<KeyTypeSV> toKeyTypeSV() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifKeyTypeSV(Consumer<KeyTypeSV> action) {
        action.accept(this);
    }
}
