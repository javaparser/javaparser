package com.github.javaparser.ast.key.sv;

import com.github.javaparser.JavaToken;
import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Arrays;
import java.util.Optional;
import java.util.function.Consumer;
import com.github.javaparser.ast.observer.ObservableProperty;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.KeyMetaConstructMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Generated;

public class KeyMetaConstruct extends Statement {

    private String kind;

    private Node child;

    private NodeList<Node> schemas = new NodeList<>();

    @AllFieldsConstructor
    public KeyMetaConstruct(String kind, Node child, NodeList<Node> schemas) {
        this.kind = kind;
        this.child = child;
        this.schemas = schemas;
    }

    public KeyMetaConstruct(TokenRange range, String kind, Node child, Node... schemas) {
        super(range);
        this.kind = kind;
        this.child = child;
        this.schemas.addAll(Arrays.asList(schemas));
    }

    public KeyMetaConstruct(TokenRange range, JavaToken kind, Node child, Node... schemas) {
        this(range, kind.getText(), child, schemas);
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
    public boolean isKeyMetaConstruct() {
        return true;
    }

    @Override
    public KeyMetaConstruct asKeyMetaConstruct() {
        return this;
    }

    @Override
    public Optional<KeyMetaConstruct> toKeyMetaConstruct() {
        return Optional.of(this);
    }

    public void ifKeyMetaConstruct(Consumer<KeyMetaConstruct> action) {
        action.accept(this);
    }

    public Node getChild() {
        return child;
    }

    public KeyMetaConstruct setChild(final Node child) {
        assertNotNull(child);
        if (child == this.child) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.CHILD, this.child, child);
        if (this.child != null)
            this.child.setParentNode(null);
        this.child = child;
        setAsParentNodeOf(child);
        return this;
    }

    public String getKind() {
        return kind;
    }

    public KeyMetaConstruct setKind(final String kind) {
        assertNotNull(kind);
        if (kind == this.kind) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.KIND, this.kind, kind);
        this.kind = kind;
        return this;
    }

    public NodeList<Node> getSchemas() {
        return schemas;
    }

    public KeyMetaConstruct setSchemas(final NodeList<Node> schemas) {
        assertNotNull(schemas);
        if (schemas == this.schemas) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.SCHEMAS, this.schemas, schemas);
        if (this.schemas != null)
            this.schemas.setParentNode(null);
        this.schemas = schemas;
        setAsParentNodeOf(schemas);
        return this;
    }

    @Override
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < schemas.size(); i++) {
            if (schemas.get(i) == node) {
                schemas.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Override
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        if (node == child) {
            setChild((Node) replacementNode);
            return true;
        }
        for (int i = 0; i < schemas.size(); i++) {
            if (schemas.get(i) == node) {
                schemas.set(i, (Node) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    public KeyMetaConstruct clone() {
        return (KeyMetaConstruct) accept(new CloneVisitor(), null);
    }

    @Override
    public KeyMetaConstructMetaModel getMetaModel() {
        return JavaParserMetaModel.keyMetaConstructMetaModel;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    public KeyMetaConstruct(TokenRange tokenRange, String kind, Node child, NodeList<Node> schemas) {
        super(tokenRange);
        setKind(kind);
        setChild(child);
        setSchemas(schemas);
        customInitialization();
    }
}
