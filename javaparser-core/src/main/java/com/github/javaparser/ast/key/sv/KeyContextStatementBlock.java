package com.github.javaparser.ast.key.sv;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.OptionalProperty;
import java.util.Optional;
import java.util.function.Consumer;
import com.github.javaparser.ast.observer.ObservableProperty;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.KeyContextStatementBlockMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Generated;

public class KeyContextStatementBlock extends Statement {

    private NodeList<Statement> statements;

    @OptionalProperty
    private KeyExecCtxtSV context;

    @OptionalProperty
    private KeyTypeSV tr;

    @OptionalProperty
    private KeyMethodSignatureSV signature;

    @OptionalProperty
    private KeyExpressionSV expression;

    @AllFieldsConstructor
    public KeyContextStatementBlock(NodeList<Statement> statements, KeyExecCtxtSV context, KeyTypeSV tr, KeyMethodSignatureSV signature, KeyExpressionSV expression) {
        this(null, statements, context, tr, signature, expression);
    }

    public KeyContextStatementBlock(TokenRange tokenRange, NodeList<Statement> statements, KeyExecCtxtSV context) {
        this(tokenRange, statements, context, null, null, null);
    }

    public KeyContextStatementBlock(TokenRange tokenRange, NodeList<Statement> statements, KeyTypeSV tr, KeyMethodSignatureSV pm, KeyExpressionSV sv) {
        this(tokenRange, statements, null, tr, pm, sv);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public KeyContextStatementBlock(TokenRange tokenRange, NodeList<Statement> statements, KeyExecCtxtSV context, KeyTypeSV tr, KeyMethodSignatureSV signature, KeyExpressionSV expression) {
        super(tokenRange);
        setStatements(statements);
        setContext(context);
        setTr(tr);
        setSignature(signature);
        setExpression(expression);
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
    public boolean isKeyContextStatementBlock() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public KeyContextStatementBlock asKeyContextStatementBlock() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<KeyContextStatementBlock> toKeyContextStatementBlock() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifKeyContextStatementBlock(Consumer<KeyContextStatementBlock> action) {
        action.accept(this);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<KeyExecCtxtSV> getContext() {
        return Optional.ofNullable(context);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public KeyContextStatementBlock setContext(final KeyExecCtxtSV context) {
        if (context == this.context) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.CONTEXT, this.context, context);
        if (this.context != null)
            this.context.setParentNode(null);
        this.context = context;
        setAsParentNodeOf(context);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<KeyExpressionSV> getExpression() {
        return Optional.ofNullable(expression);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public KeyContextStatementBlock setExpression(final KeyExpressionSV expression) {
        if (expression == this.expression) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.EXPRESSION, this.expression, expression);
        if (this.expression != null)
            this.expression.setParentNode(null);
        this.expression = expression;
        setAsParentNodeOf(expression);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<KeyMethodSignatureSV> getSignature() {
        return Optional.ofNullable(signature);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public KeyContextStatementBlock setSignature(final KeyMethodSignatureSV signature) {
        if (signature == this.signature) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.SIGNATURE, this.signature, signature);
        if (this.signature != null)
            this.signature.setParentNode(null);
        this.signature = signature;
        setAsParentNodeOf(signature);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Statement> getStatements() {
        return statements;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public KeyContextStatementBlock setStatements(final NodeList<Statement> statements) {
        assertNotNull(statements);
        if (statements == this.statements) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.STATEMENTS, this.statements, statements);
        if (this.statements != null)
            this.statements.setParentNode(null);
        this.statements = statements;
        setAsParentNodeOf(statements);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<KeyTypeSV> getTr() {
        return Optional.ofNullable(tr);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public KeyContextStatementBlock setTr(final KeyTypeSV tr) {
        if (tr == this.tr) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.TR, this.tr, tr);
        if (this.tr != null)
            this.tr.setParentNode(null);
        this.tr = tr;
        setAsParentNodeOf(tr);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public KeyContextStatementBlock removeContext() {
        return setContext((KeyExecCtxtSV) null);
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public KeyContextStatementBlock removeExpression() {
        return setExpression((KeyExpressionSV) null);
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public KeyContextStatementBlock removeSignature() {
        return setSignature((KeyMethodSignatureSV) null);
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public KeyContextStatementBlock removeTr() {
        return setTr((KeyTypeSV) null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        if (context != null) {
            if (node == context) {
                removeContext();
                return true;
            }
        }
        if (expression != null) {
            if (node == expression) {
                removeExpression();
                return true;
            }
        }
        if (signature != null) {
            if (node == signature) {
                removeSignature();
                return true;
            }
        }
        for (int i = 0; i < statements.size(); i++) {
            if (statements.get(i) == node) {
                statements.remove(i);
                return true;
            }
        }
        if (tr != null) {
            if (node == tr) {
                removeTr();
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
        if (context != null) {
            if (node == context) {
                setContext((KeyExecCtxtSV) replacementNode);
                return true;
            }
        }
        if (expression != null) {
            if (node == expression) {
                setExpression((KeyExpressionSV) replacementNode);
                return true;
            }
        }
        if (signature != null) {
            if (node == signature) {
                setSignature((KeyMethodSignatureSV) replacementNode);
                return true;
            }
        }
        for (int i = 0; i < statements.size(); i++) {
            if (statements.get(i) == node) {
                statements.set(i, (Statement) replacementNode);
                return true;
            }
        }
        if (tr != null) {
            if (node == tr) {
                setTr((KeyTypeSV) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public KeyContextStatementBlock clone() {
        return (KeyContextStatementBlock) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public KeyContextStatementBlockMetaModel getMetaModel() {
        return JavaParserMetaModel.keyContextStatementBlockMetaModel;
    }
}
