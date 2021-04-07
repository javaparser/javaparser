package com.github.javaparser.ast.jml.body;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.ast.observer.ObservableProperty;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.JmlMethodDeclarationMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Generated;

/**
 * @author Alexander Weigl
 * @version 1 (4/5/21)
 */
public class JmlMethodDeclaration extends JmlClassLevel {

    private MethodDeclaration methodDeclaration;

    public JmlMethodDeclaration() {
        this(null);
    }

    @AllFieldsConstructor
    public JmlMethodDeclaration(MethodDeclaration methodDeclaration) {
        this(null, methodDeclaration);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlMethodDeclaration(TokenRange tokenRange, MethodDeclaration methodDeclaration) {
        super(tokenRange);
        setMethodDeclaration(methodDeclaration);
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

    public MethodDeclaration getMethodDeclaration() {
        return methodDeclaration;
    }

    public JmlMethodDeclaration setMethodDeclaration(final MethodDeclaration methodDeclaration) {
        assertNotNull(methodDeclaration);
        if (methodDeclaration == this.methodDeclaration) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.METHOD_DECLARATION, this.methodDeclaration, methodDeclaration);
        if (this.methodDeclaration != null)
            this.methodDeclaration.setParentNode(null);
        this.methodDeclaration = methodDeclaration;
        setAsParentNodeOf(methodDeclaration);
        return this;
    }

    @Override
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Override
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        if (node == methodDeclaration) {
            setMethodDeclaration((MethodDeclaration) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    public JmlMethodDeclaration clone() {
        return (JmlMethodDeclaration) accept(new CloneVisitor(), null);
    }

    @Override
    public JmlMethodDeclarationMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlMethodDeclarationMetaModel;
    }
}
