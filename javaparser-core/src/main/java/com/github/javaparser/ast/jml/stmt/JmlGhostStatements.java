package com.github.javaparser.ast.jml.stmt;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Optional;
import java.util.function.Consumer;
import com.github.javaparser.ast.observer.ObservableProperty;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.JmlGhostStatementsMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Generated;

/**
 * @author Alexander Weigl
 * @version 1 (3/26/21)
 */
public class JmlGhostStatements extends JmlStatement {

    private NodeList<Statement> statements;

    @AllFieldsConstructor
    public JmlGhostStatements(NodeList<Statement> statements) {
        this.statements = statements;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlGhostStatements(TokenRange tokenRange, NodeList<Statement> statements) {
        super(tokenRange);
        setStatements(statements);
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
    public boolean isJmlGhostStatements() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlGhostStatements asJmlGhostStatements() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlGhostStatements> toJmlGhostStatements() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlGhostStatements(Consumer<JmlGhostStatements> action) {
        action.accept(this);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Statement> getStatements() {
        return statements;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlGhostStatements setStatements(final NodeList<Statement> statements) {
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

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null) {
            return false;
        }
        for (int i = 0; i < statements.size(); i++) {
            if (statements.get(i) == node) {
                statements.remove(i);
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
        for (int i = 0; i < statements.size(); i++) {
            if (statements.get(i) == node) {
                statements.set(i, (Statement) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlGhostStatements clone() {
        return (JmlGhostStatements) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlGhostStatementsMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlGhostStatementsMetaModel;
    }
}
