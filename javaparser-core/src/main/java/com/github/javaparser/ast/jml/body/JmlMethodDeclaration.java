package com.github.javaparser.ast.jml.body;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.jml.clauses.JmlContract;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.ast.observer.ObservableProperty;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.JmlMethodDeclarationMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.metamodel.OptionalProperty;
import java.util.Optional;

/**
 * @author Alexander Weigl
 * @version 1 (4/5/21)
 */
public class JmlMethodDeclaration extends JmlClassLevel {

    private MethodDeclaration methodDeclaration;

    @OptionalProperty
    private JmlContract contract;

    public JmlMethodDeclaration() {
        this(null, null);
    }

    @AllFieldsConstructor
    public JmlMethodDeclaration(MethodDeclaration methodDeclaration, JmlContract contract) {
        this(null, methodDeclaration, contract);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlMethodDeclaration(TokenRange tokenRange, MethodDeclaration methodDeclaration, JmlContract contract) {
        super(tokenRange);
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
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        if (contract != null) {
            if (node == contract) {
                removeContract();
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
        if (contract != null) {
            if (node == contract) {
                setContract((JmlContract) replacementNode);
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

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlMethodDeclarationMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlMethodDeclarationMetaModel;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<JmlContract> getContract() {
        return Optional.ofNullable(contract);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlMethodDeclaration setContract(final JmlContract contract) {
        if (contract == this.contract) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.CONTRACT, this.contract, contract);
        if (this.contract != null)
            this.contract.setParentNode(null);
        this.contract = contract;
        setAsParentNodeOf(contract);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public JmlMethodDeclaration removeContract() {
        return setContract((JmlContract) null);
    }
}
