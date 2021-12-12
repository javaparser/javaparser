package com.github.javaparser.ast.jml.body;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Optional;
import java.util.function.Consumer;
import com.github.javaparser.ast.observer.ObservableProperty;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.JmlFieldDeclarationMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Generated;

/**
 * @author Alexander Weigl
 * @version 1 (3/11/21)
 */
public class JmlFieldDeclaration extends JmlClassLevel<JmlFieldDeclaration> {

    private FieldDeclaration decl;

    public JmlFieldDeclaration() {
        this(null);
    }

    @AllFieldsConstructor
    public JmlFieldDeclaration(FieldDeclaration decl) {
        this(null, decl);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlFieldDeclaration(TokenRange tokenRange, FieldDeclaration decl) {
        super(tokenRange);
        setDecl(decl);
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
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJmlFieldDeclaration() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlFieldDeclaration asJmlFieldDeclaration() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlFieldDeclaration> toJmlFieldDeclaration() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlFieldDeclaration(Consumer<JmlFieldDeclaration> action) {
        action.accept(this);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public FieldDeclaration getDecl() {
        return decl;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlFieldDeclaration setDecl(final FieldDeclaration decl) {
        assertNotNull(decl);
        if (decl == this.decl) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.DECL, this.decl, decl);
        if (this.decl != null)
            this.decl.setParentNode(null);
        this.decl = decl;
        setAsParentNodeOf(decl);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null) {
            return false;
        }
        if (node == decl) {
            setDecl((FieldDeclaration) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlFieldDeclaration clone() {
        return (JmlFieldDeclaration) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlFieldDeclarationMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlFieldDeclarationMetaModel;
    }
}
