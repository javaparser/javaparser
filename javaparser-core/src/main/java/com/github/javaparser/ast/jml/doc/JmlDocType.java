package com.github.javaparser.ast.jml.doc;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;

import java.util.Optional;
import java.util.function.Consumer;

import com.github.javaparser.ast.observer.ObservableProperty;

import static com.github.javaparser.utils.Utils.assertNotNull;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.JmlDocTypeMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Generated;

/**
 * @author Alexander Weigl
 * @version 1 (11/23/21)
 */
public class JmlDocType extends TypeDeclaration<JmlDocType> {

    private NodeList<JmlDoc> jmlComments;

    @AllFieldsConstructor
    public JmlDocType(NodeList<JmlDoc> jmlComments) {
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
    public ResolvedReferenceTypeDeclaration resolve() {
        return null;
    }

    @Override
    public boolean isJmlDocType() {
        return true;
    }

    @Override
    public JmlDocType asJmlDocType() {
        return this;
    }

    @Override
    public Optional<JmlDocType> toJmlDocType() {
        return Optional.of(this);
    }

    public void ifJmlDocType(Consumer<JmlDocType> action) {
        action.accept(this);
    }

    public NodeList<JmlDoc> getJmlComments() {
        return jmlComments;
    }

    public JmlDocType setJmlComments(final NodeList<JmlDoc> jmlComments) {
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

    @Override
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < jmlComments.size(); i++) {
            if (jmlComments.get(i) == node) {
                jmlComments.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Override
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        for (int i = 0; i < jmlComments.size(); i++) {
            if (jmlComments.get(i) == node) {
                jmlComments.set(i, (JmlDoc) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    public JmlDocType clone() {
        return (JmlDocType) accept(new CloneVisitor(), null);
    }

    @Override
    public JmlDocTypeMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlDocTypeMetaModel;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    public JmlDocType(TokenRange tokenRange, NodeList<JmlDoc> jmlComments) {
        super(tokenRange, null, null, new SimpleName(""), new NodeList<>());
        setJmlComments(jmlComments);
        customInitialization();
    }
}
