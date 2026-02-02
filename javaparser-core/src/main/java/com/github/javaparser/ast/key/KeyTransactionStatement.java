package com.github.javaparser.ast.key;

import com.github.javaparser.JavaToken;
import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.KeyTransactionStatementMetaModel;
import java.util.Optional;
import java.util.function.Consumer;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import java.util.Objects;
import org.jspecify.annotations.NonNull;

public class KeyTransactionStatement extends Statement {

    private TransactionType type;

    @AllFieldsConstructor
    public KeyTransactionStatement(TransactionType type) {
        this.type = type;
    }

    public KeyTransactionStatement(TokenRange range, JavaToken begin) {
        super(range);
        setType(TransactionType.byName(begin.getText()));
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

    public enum TransactionType {

        BEGIN("#beginJavaCardTransaction"), COMMIT("#commitJavaCardTransaction"), FINISH("#finishJavaCardTransaction"), ABORT("#abortJavaCardTransaction");

        public final String symbol;

        TransactionType(String symbol) {
            this.symbol = symbol;
        }

        public static TransactionType byName(String text) {
            for (TransactionType value : values()) {
                if (value.symbol.equals(text)) {
                    return value;
                }
            }
            return null;
        }
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public TransactionType getType() {
        return type;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public KeyTransactionStatement setType(final @NonNull() TransactionType type) {
        assertNotNull(type);
        if (type == this.type) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.TYPE, this.type, type);
        this.type = type;
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public KeyTransactionStatement clone() {
        return (KeyTransactionStatement) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public KeyTransactionStatementMetaModel getMetaModel() {
        return JavaParserMetaModel.keyTransactionStatementMetaModel;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public KeyTransactionStatement(TokenRange tokenRange, TransactionType type) {
        super(tokenRange);
        setType(type);
        customInitialization();
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isKeyTransactionStatement() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public KeyTransactionStatement asKeyTransactionStatement() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<KeyTransactionStatement> toKeyTransactionStatement() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifKeyTransactionStatement(Consumer<KeyTransactionStatement> action) {
        action.accept(this);
    }

    @com.github.javaparser.ast.key.IgnoreLexPrinting()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public @NonNull() TransactionType type() {
        return Objects.requireNonNull(type);
    }
}
