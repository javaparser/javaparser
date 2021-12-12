package com.github.javaparser.ast.jml.stmt;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import static com.github.javaparser.utils.Utils.assertNotNull;
import java.util.Optional;
import java.util.function.Consumer;
import com.github.javaparser.metamodel.JmlGhostStatementMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

/**
 * @author Alexander Weigl
 * @version 1 (3/26/21)
 */
public class JmlGhostStatement extends JmlStatement {

    private Statement statement;

    @AllFieldsConstructor
    public JmlGhostStatement(Statement statement) {
        this.statement = statement;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlGhostStatement(TokenRange tokenRange, Statement statement) {
        super(tokenRange);
        setStatement(statement);
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
    public Statement getStatement() {
        return statement;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlGhostStatement setstatement(final Statement statement) {
        assertNotNull(statement);
        if (statement == this.statement) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.STATEMENT, this.statement, statement);
        if (this.statement != null)
            this.statement.setParentNode(null);
        this.statement = statement;
        setAsParentNodeOf(statement);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null) {
            return false;
        }
        if (node == statement) {
            setStatement((Statement) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlGhostStatement clone() {
        return (JmlGhostStatement) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJmlGhostStatement() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlGhostStatement asJmlGhostStatement() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlGhostStatement> toJmlGhostStatement() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlGhostStatement(Consumer<JmlGhostStatement> action) {
        action.accept(this);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlGhostStatement setStatement(final Statement statement) {
        assertNotNull(statement);
        if (statement == this.statement) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.STATEMENT, this.statement, statement);
        if (this.statement != null)
            this.statement.setParentNode(null);
        this.statement = statement;
        setAsParentNodeOf(statement);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlGhostStatementMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlGhostStatementMetaModel;
    }
}
