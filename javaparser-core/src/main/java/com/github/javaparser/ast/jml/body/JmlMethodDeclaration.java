package com.github.javaparser.ast.jml.body;

import static com.github.javaparser.utils.Utils.assertNotNull;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.jml.clauses.JmlContract;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.JmlMethodDeclarationMetaModel;
import com.github.javaparser.metamodel.OptionalProperty;
import java.util.Objects;
import java.util.Optional;
import java.util.function.Consumer;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * @author Alexander Weigl
 * @version 1 (4/5/21)
 */
public class JmlMethodDeclaration extends JmlClassLevelDeclaration<JmlMethodDeclaration> {

    private MethodDeclaration methodDeclaration;

    @OptionalProperty
    private JmlContract contract;

    private NodeList<SimpleName> jmlTags;

    public JmlMethodDeclaration() {
        this(null, new NodeList<>(), new MethodDeclaration(), null);
    }

    @AllFieldsConstructor
    public JmlMethodDeclaration(
            NodeList<SimpleName> jmlTags, MethodDeclaration methodDeclaration, JmlContract contract) {
        this(null, jmlTags, methodDeclaration, contract);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlMethodDeclaration(
            TokenRange tokenRange,
            NodeList<SimpleName> jmlTags,
            MethodDeclaration methodDeclaration,
            JmlContract contract) {
        super(tokenRange);
        setJmlTags(jmlTags);
        setMethodDeclaration(methodDeclaration);
        setContract(contract);
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
    public MethodDeclaration getMethodDeclaration() {
        return methodDeclaration;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlMethodDeclaration setMethodDeclaration(final @NonNull() MethodDeclaration methodDeclaration) {
        assertNotNull(methodDeclaration);
        if (methodDeclaration == this.methodDeclaration) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.METHOD_DECLARATION, this.methodDeclaration, methodDeclaration);
        if (this.methodDeclaration != null) this.methodDeclaration.setParentNode(null);
        this.methodDeclaration = methodDeclaration;
        setAsParentNodeOf(methodDeclaration);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null) {
            return false;
        }
        if (contract != null) {
            if (node == contract) {
                removeContract();
                return true;
            }
        }
        for (int i = 0; i < jmlTags.size(); i++) {
            if (jmlTags.get(i) == node) {
                jmlTags.remove(i);
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
        if (contract != null) {
            if (node == contract) {
                setContract((JmlContract) replacementNode);
                return true;
            }
        }
        for (int i = 0; i < jmlTags.size(); i++) {
            if (jmlTags.get(i) == node) {
                jmlTags.set(i, (SimpleName) replacementNode);
                return true;
            }
        }
        if (node == methodDeclaration) {
            setMethodDeclaration((MethodDeclaration) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlMethodDeclaration clone() {
        return (JmlMethodDeclaration) accept(new CloneVisitor(), null);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<JmlContract> getContract() {
        return Optional.ofNullable(contract);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlMethodDeclaration setContract(final @Nullable() JmlContract contract) {
        if (contract == this.contract) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.CONTRACT, this.contract, contract);
        if (this.contract != null) this.contract.setParentNode(null);
        this.contract = contract;
        setAsParentNodeOf(contract);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public JmlMethodDeclaration removeContract() {
        return setContract((JmlContract) null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlMethodDeclarationMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlMethodDeclarationMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<SimpleName> getJmlTags() {
        return jmlTags;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlMethodDeclaration setJmlTags(final @NonNull() NodeList<SimpleName> jmlTags) {
        assertNotNull(jmlTags);
        if (jmlTags == this.jmlTags) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.JML_TAGS, this.jmlTags, jmlTags);
        if (this.jmlTags != null) this.jmlTags.setParentNode(null);
        this.jmlTags = jmlTags;
        setAsParentNodeOf(jmlTags);
        return this;
    }

    @com.github.javaparser.ast.key.IgnoreLexPrinting()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public @Nullable() JmlContract contract() {
        return contract;
    }

    @com.github.javaparser.ast.key.IgnoreLexPrinting()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public @NonNull() NodeList<SimpleName> jmlTags() {
        return Objects.requireNonNull(jmlTags);
    }

    @com.github.javaparser.ast.key.IgnoreLexPrinting()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public @NonNull() MethodDeclaration methodDeclaration() {
        return Objects.requireNonNull(methodDeclaration);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJmlMethodDeclaration() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlMethodDeclaration asJmlMethodDeclaration() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlMethodDeclaration> toJmlMethodDeclaration() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlMethodDeclaration(Consumer<JmlMethodDeclaration> action) {
        action.accept(this);
    }
}
