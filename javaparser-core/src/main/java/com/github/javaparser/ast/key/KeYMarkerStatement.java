package com.github.javaparser.ast.key;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.DataKey;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.KeYMarkerStatementMetaModel;
import java.util.Objects;
import java.util.Optional;
import java.util.function.Consumer;

/**
 * This class is statement, that can be plugged everywhere. Its meaning is defined by {@link #kind} with semantics
 * left to the user. For additional value, use {@link #setData(DataKey, Object)} and {@link #getData(DataKey)}.
 *
 * @author Alexander Weigl
 * @version 1 (3/4/26)
 */
public class KeYMarkerStatement extends Statement {

    private int kind = 0;

    @AllFieldsConstructor
    public KeYMarkerStatement(int kind) {
        this.kind = kind;
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
    public boolean isKeYMarkerStatement() {
        return true;
    }

    @Override
    public KeYMarkerStatement asKeYMarkerStatement() {
        return this;
    }

    @Override
    public Optional<KeYMarkerStatement> toKeYMarkerStatement() {
        return Optional.of(this);
    }

    public void ifKeYMarkerStatement(Consumer<KeYMarkerStatement> action) {
        action.accept(this);
    }

    public int getKind() {
        return kind;
    }

    @com.github.javaparser.ast.key.IgnoreLexPrinting()
    public int kind() {
        return Objects.requireNonNull(kind);
    }

    public KeYMarkerStatement setKind(final int kind) {
        if (kind == this.kind) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.KIND, this.kind, kind);
        this.kind = kind;
        return this;
    }

    @Override
    public KeYMarkerStatement clone() {
        return (KeYMarkerStatement) accept(new CloneVisitor(), null);
    }

    @Override
    public KeYMarkerStatementMetaModel getMetaModel() {
        return JavaParserMetaModel.keYMarkerStatementMetaModel;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    public KeYMarkerStatement(TokenRange tokenRange, int kind) {
        super(tokenRange);
        setKind(kind);
        customInitialization();
    }
}
