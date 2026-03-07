package com.github.javaparser.ast.key;

import static com.github.javaparser.utils.Utils.assertNotNull;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.JmlDocsStatementsMetaModel;
import java.util.Objects;
import java.util.Optional;
import java.util.function.Consumer;
import org.jspecify.annotations.NonNull;

/**
 * @author Alexander Weigl
 * @version 1 (3/3/26)
 */
public class JmlDocsStatements extends Statement {

    private NodeList<JmlDoc> jmlDocs;

    @AllFieldsConstructor
    public JmlDocsStatements(NodeList<JmlDoc> jmlDocs) {
        this(JmlDocsBodyDeclaration.getRange(jmlDocs), jmlDocs);
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
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJmlDocsStatements() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlDocsStatements asJmlDocsStatements() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlDocsStatements> toJmlDocsStatements() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlDocsStatements(Consumer<JmlDocsStatements> action) {
        action.accept(this);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<JmlDoc> getJmlDocs() {
        return jmlDocs;
    }

    @com.github.javaparser.ast.key.IgnoreLexPrinting()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public @NonNull() NodeList<JmlDoc> jmlDocs() {
        return Objects.requireNonNull(jmlDocs);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlDocsStatements setJmlDocs(final @NonNull() NodeList<JmlDoc> jmlDocs) {
        assertNotNull(jmlDocs);
        if (jmlDocs == this.jmlDocs) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.JML_DOCS, this.jmlDocs, jmlDocs);
        if (this.jmlDocs != null) this.jmlDocs.setParentNode(null);
        this.jmlDocs = jmlDocs;
        setAsParentNodeOf(jmlDocs);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null) {
            return false;
        }
        for (int i = 0; i < jmlDocs.size(); i++) {
            if (jmlDocs.get(i) == node) {
                jmlDocs.remove(i);
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
        for (int i = 0; i < jmlDocs.size(); i++) {
            if (jmlDocs.get(i) == node) {
                jmlDocs.set(i, (JmlDoc) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlDocsStatements clone() {
        return (JmlDocsStatements) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlDocsStatementsMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlDocsStatementsMetaModel;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlDocsStatements(TokenRange tokenRange, NodeList<JmlDoc> jmlDocs) {
        super(tokenRange);
        setJmlDocs(jmlDocs);
        customInitialization();
    }
}
