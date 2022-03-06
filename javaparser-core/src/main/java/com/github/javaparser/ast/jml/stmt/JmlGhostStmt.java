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
import com.github.javaparser.metamodel.JmlGhostStmtMetaModel;

/**
 * @author Alexander Weigl
 * @version 1 (3/26/21)
 */
public class JmlGhostStmt extends JmlStatement {

    private Statement statement;

    @AllFieldsConstructor
    public JmlGhostStmt(Statement statement) {
        this.statement = statement;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlGhostStmt(TokenRange tokenRange, Statement statement) {
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
    public JmlGhostStmt setstatement(final Statement statement) {
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
    public JmlGhostStmt clone() {
        return (JmlGhostStmt) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJmlGhostStatement() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlGhostStmt asJmlGhostStatement() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlGhostStmt> toJmlGhostStatement() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlGhostStatement(Consumer<JmlGhostStmt> action) {
        action.accept(this);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlGhostStmt setStatement(final Statement statement) {
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
    public JmlGhostStmtMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlGhostStmtMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJmlGhostStmt() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlGhostStmt asJmlGhostStmt() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlGhostStmt> toJmlGhostStmt() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlGhostStmt(Consumer<JmlGhostStmt> action) {
        action.accept(this);
    }
}
