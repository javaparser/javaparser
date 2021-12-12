package com.github.javaparser.ast.jml.clauses;

import com.github.javaparser.JavaToken;
import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Jmlish;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.JmlClauseMetaModel;
import java.util.Arrays;
import java.util.Optional;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Alexander Weigl
 * @version 1 (2/21/21)
 */
public abstract class JmlClause extends Node implements Jmlish {

    private JmlClauseKind kind;

    public JmlClause() {
        this((TokenRange) null);
    }

    @AllFieldsConstructor
    public JmlClause(final JmlClauseKind kind) {
        this(null, kind);
    }

    protected final void setKindByToken(JavaToken token) {
        Optional<JmlClauseKind> k = Arrays.stream(JmlClauseKind.values()).filter(it -> it.jmlSymbol.equals(token.getText())).findFirst();
        if (k.isPresent()) {
            kind = k.get();
        } else {
            throw new IllegalArgumentException("Could not find clause kind for: " + token.getText());
        }
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlClause(TokenRange tokenRange) {
        super(tokenRange);
        customInitialization();
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlClause clone() {
        return (JmlClause) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlClauseMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlClauseMetaModel;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlClauseKind getKind() {
        return kind;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlClause setKind(final JmlClauseKind kind) {
        assertNotNull(kind);
        if (kind == this.kind) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.KIND, this.kind, kind);
        this.kind = kind;
        return this;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlClause(TokenRange tokenRange, JmlClauseKind kind) {
        super(tokenRange);
        setKind(kind);
        customInitialization();
    }
}
