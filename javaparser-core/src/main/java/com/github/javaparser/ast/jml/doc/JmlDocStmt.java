package com.github.javaparser.ast.jml.doc;

import com.github.javaparser.JavaToken;
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
import com.github.javaparser.metamodel.JmlDocStmtMetaModel;
import java.util.Optional;
import java.util.function.Consumer;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Alexander Weigl
 * @version 1 (11/23/21)
 */
public class JmlDocStmt extends Statement {

    private NodeList<JmlDoc> jmlComments;

    @AllFieldsConstructor
    public JmlDocStmt(NodeList<JmlDoc> jmlComments) {
        super(null);
        this.jmlComments = jmlComments;
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
    public boolean isJmlDocStmt() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlDocStmt asJmlDocStmt() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlDocStmt> toJmlDocStmt() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlDocStmt(Consumer<JmlDocStmt> action) {
        action.accept(this);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<JmlDoc> getJmlComments() {
        return jmlComments;
    }

    public JmlDocStmt setJmlComments(final JavaToken jmlComments) {
        assertNotNull(jmlComments);
        notifyPropertyChange(ObservableProperty.JML_COMMENTS, this.jmlComments, jmlComments);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null) {
            return false;
        }
        for (int i = 0; i < jmlComments.size(); i++) {
            if (jmlComments.get(i) == node) {
                jmlComments.remove(i);
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
        for (int i = 0; i < jmlComments.size(); i++) {
            if (jmlComments.get(i) == node) {
                jmlComments.set(i, (JmlDoc) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlDocStmt clone() {
        return (JmlDocStmt) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlDocStmtMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlDocStmtMetaModel;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    public JmlDocStmt(TokenRange tokenRange, JavaToken jmlComments) {
        super(tokenRange);
        setJmlComments(jmlComments);
        customInitialization();
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlDocStmt setJmlComments(final NodeList<JmlDoc> jmlComments) {
        assertNotNull(jmlComments);
        if (jmlComments == this.jmlComments) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.JML_COMMENTS, this.jmlComments, jmlComments);
        if (this.jmlComments != null)
            this.jmlComments.setParentNode(null);
        this.jmlComments = jmlComments;
        setAsParentNodeOf(jmlComments);
        return this;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlDocStmt(TokenRange tokenRange, NodeList<JmlDoc> jmlComments) {
        super(tokenRange);
        setJmlComments(jmlComments);
        customInitialization();
    }
}
