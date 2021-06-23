package com.github.javaparser.ast.jml.locref;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.jml.JmlKeyword;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.ast.observer.ObservableProperty;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.LocationSetPrimaryMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Generated;
import java.util.Optional;
import java.util.function.Consumer;

/**
 * @author Alexander Weigl
 * @version 1 (3/20/21)
 */
public class LocationSetPrimary extends LocationSetExpression {

    public enum Kind implements JmlKeyword {

        EVERYTHING, NOTHING, STRICTLY_NOTHING, NOT_SPECIFIED, EMPTYSET;

        private final String symbol;

        Kind() {
            this.symbol = "\\" + name().toLowerCase();
        }

        Kind(String symbol) {
            this.symbol = symbol;
        }

        @Override
        public String jmlSymbol() {
            return symbol;
        }
    }

    private Kind kind;

    public LocationSetPrimary() {
    }

    @AllFieldsConstructor
    public LocationSetPrimary(Kind kind) {
        this.kind = kind;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public LocationSetPrimary(TokenRange tokenRange, Kind kind) {
        super(tokenRange);
        setKind(kind);
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
    public Kind getKind() {
        return kind;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public LocationSetPrimary setKind(final Kind kind) {
        assertNotNull(kind);
        if (kind == this.kind) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.KIND, this.kind, kind);
        this.kind = kind;
        return this;
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
    public LocationSetPrimary clone() {
        return (LocationSetPrimary) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public LocationSetPrimaryMetaModel getMetaModel() {
        return JavaParserMetaModel.locationSetPrimaryMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isLocationSetPrimary() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public LocationSetPrimary asLocationSetPrimary() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<LocationSetPrimary> toLocationSetPrimary() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifLocationSetPrimary(Consumer<LocationSetPrimary> action) {
        action.accept(this);
    }
}
