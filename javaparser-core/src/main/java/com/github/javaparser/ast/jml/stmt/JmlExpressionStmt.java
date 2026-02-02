package com.github.javaparser.ast.jml.stmt;

import static com.github.javaparser.utils.Utils.assertNotNull;

import com.github.javaparser.GeneratedJavaParserConstants;
import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.jml.JmlKeyword;
import com.github.javaparser.ast.jml.NodeWithJmlTags;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.JmlExpressionStmtMetaModel;
import java.util.Arrays;
import java.util.Objects;
import java.util.Optional;
import java.util.function.Consumer;
import org.jspecify.annotations.NonNull;

/**
 * @author Alexander Weigl
 * @version 1 (2/21/21)
 */
public class JmlExpressionStmt extends JmlStatement implements NodeWithJmlTags<JmlExpressionStmt> {

    public enum JmlStmtKind implements JmlKeyword {
        ASSERT(GeneratedJavaParserConstants.ASSERT),
        ASSERT_REDUNDANTLY(GeneratedJavaParserConstants.ASSERT_REDUNDANTLY),
        ASSUME(GeneratedJavaParserConstants.ASSUME),
        ASSUME_REDUNDANTLY(GeneratedJavaParserConstants.ASSUME_REDUNDANTLY),
        HENCE_BY(GeneratedJavaParserConstants.HENCE_BY),
        HENCE_BY_REDUNDANTLY(GeneratedJavaParserConstants.HENCE_BY_REDUNDANTLY),
        SET(GeneratedJavaParserConstants.SET);

        final int tokenType;

        JmlStmtKind(int tokenType) {
            this.tokenType = tokenType;
        }

        @Override
        public String jmlSymbol() {
            return name().toLowerCase();
        }
    }

    private JmlStmtKind kind;

    private Expression expression;

    private NodeList<SimpleName> jmlTags;

    @AllFieldsConstructor
    public JmlExpressionStmt(NodeList<SimpleName> jmlTags, final JmlStmtKind kind, final Expression expression) {
        this(null, jmlTags, kind, expression);
    }

    public JmlExpressionStmt(TokenRange range, NodeList<SimpleName> jmlTags, final Expression expression) {
        this(range, jmlTags, JmlStmtKind.ASSERT, expression);
        int tt = range.getBegin().getKind();
        Optional<JmlStmtKind> k = Arrays.stream(JmlStmtKind.values())
                .filter(i -> i.tokenType == tt)
                .findFirst();
        k.ifPresent(this::setKind);
        if (!k.isPresent()) {
            throw new IllegalArgumentException("wrong token type");
        }
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
    public boolean isJmlAssertStmt() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlExpressionStmt asJmlAssertStmt() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlExpressionStmt> toJmlAssertStmt() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlAssertStmt(Consumer<JmlExpressionStmt> action) {
        action.accept(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null) {
            return false;
        }
        if (node == expression) {
            setExpression((Expression) replacementNode);
            return true;
        }
        for (int i = 0; i < jmlTags.size(); i++) {
            if (jmlTags.get(i) == node) {
                jmlTags.set(i, (SimpleName) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlExpressionStmt clone() {
        return (JmlExpressionStmt) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlExpressionStmtMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlExpressionStmtMetaModel;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlExpressionStmt(TokenRange tokenRange) {
        super(tokenRange);
        customInitialization();
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Expression getExpression() {
        return expression;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlExpressionStmt setExpression(final Expression expression) {
        assertNotNull(expression);
        if (expression == this.expression) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.EXPRESSION, this.expression, expression);
        if (this.expression != null) this.expression.setParentNode(null);
        this.expression = expression;
        setAsParentNodeOf(expression);
        return this;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlExpressionStmt(
            TokenRange tokenRange, NodeList<SimpleName> jmlTags, JmlStmtKind kind, Expression expression) {
        super(tokenRange);
        setJmlTags(jmlTags);
        setKind(kind);
        setExpression(expression);
        customInitialization();
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJmlStmtWithExpression() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlExpressionStmt asJmlStmtWithExpression() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlExpressionStmt> toJmlStmtWithExpression() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlStmtWithExpression(Consumer<JmlExpressionStmt> action) {
        action.accept(this);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlStmtKind getKind() {
        return kind;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlExpressionStmt setKind(final JmlStmtKind kind) {
        assertNotNull(kind);
        if (kind == this.kind) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.KIND, this.kind, kind);
        this.kind = kind;
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJmlExpressionStmt() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlExpressionStmt asJmlExpressionStmt() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlExpressionStmt> toJmlExpressionStmt() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlExpressionStmt(Consumer<JmlExpressionStmt> action) {
        action.accept(this);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<SimpleName> getJmlTags() {
        return jmlTags;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlExpressionStmt setJmlTags(final NodeList<SimpleName> jmlTags) {
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

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null) {
            return false;
        }
        for (int i = 0; i < jmlTags.size(); i++) {
            if (jmlTags.get(i) == node) {
                jmlTags.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @NonNull()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Expression expression() {
        return Objects.requireNonNull(expression);
    }

    @NonNull()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<SimpleName> jmlTags() {
        return Objects.requireNonNull(jmlTags);
    }

    @NonNull()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlStmtKind kind() {
        return Objects.requireNonNull(kind);
    }
}
