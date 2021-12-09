package com.github.javaparser.ast.jml.doc;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.JmlDocTypeMetaModel;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import java.util.Optional;
import java.util.function.Consumer;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Alexander Weigl
 * @version 1 (11/23/21)
 */
public class JmlDocType extends TypeDeclaration<JmlDocType> {

    private NodeList<JmlDoc> jmlComments;

    public JmlDocType(NodeList<JmlDoc> jmlComments) {
        this.jmlComments = jmlComments;
    }

    @AllFieldsConstructor
    public JmlDocType(NodeList<Modifier> modifiers, NodeList<AnnotationExpr> annotations, SimpleName name, NodeList<BodyDeclaration<?>> members, NodeList<JmlDoc> jmlComments) {
        super(modifiers, annotations, name, members);
        this.jmlComments = jmlComments;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlDocType(TokenRange tokenRange, NodeList<JmlDoc> jmlComments) {
        setJmlComments(jmlComments);
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

    @Override
    public ResolvedReferenceTypeDeclaration resolve() {
        return null;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJmlDocType() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlDocType asJmlDocType() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlDocType> toJmlDocType() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlDocType(Consumer<JmlDocType> action) {
        action.accept(this);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<JmlDoc> getJmlComments() {
        return jmlComments;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
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
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
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
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
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
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlDocType clone() {
        return (JmlDocType) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlDocTypeMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlDocTypeMetaModel;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlDocType(TokenRange tokenRange, NodeList<Modifier> modifiers, NodeList<AnnotationExpr> annotations, SimpleName name, NodeList<BodyDeclaration<?>> members, NodeList<JmlDoc> jmlComments) {
        super(tokenRange, modifiers, annotations, name, members);
        setJmlComments(jmlComments);
        customInitialization();
    }
}
