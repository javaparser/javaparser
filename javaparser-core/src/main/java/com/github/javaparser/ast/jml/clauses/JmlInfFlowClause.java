package com.github.javaparser.ast.jml.clauses;

import com.github.javaparser.JavaToken;
import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithOptionalSimpleName;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.OptionalProperty;
import org.jspecify.annotations.NullMarked;
import java.util.Objects;
import org.jspecify.annotations.NonNull;
import com.github.javaparser.ast.observer.ObservableProperty;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.JmlInfFlowClauseMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Generated;

/// ```
/// determines_clause
///   : (DETERMINES | SEPARATES | LOOP_SEPARATES | LOOP_DETERMINES )
///     determined=infflowspeclist
///     BY (byItself=ITSELF|by=infflowspeclist)
///     ( DECLASSIFIES decl+=infflowspeclist
///     | ERASES       erases+=infflowspeclist
///     | NEW_OBJECTS newObs+=infflowspeclist
///     )*
///     SEMI_TOPLEVEL
///   ;
/// ```
///
/// @author Alexander Weigl
/// @version 1 (3/18/26)
@NullMarked
public class JmlInfFlowClause extends JmlClause {

    private JmlClauseKind kind;

    private NodeList<Expression> expressions;

    private NodeList<Expression> by;

    private NodeList<Expression> declassifies;

    private NodeList<Expression> erases;

    private NodeList<Expression> newObjects;

    @AllFieldsConstructor
    public JmlInfFlowClause(JmlClauseKind kind, SimpleName name, NodeList<Expression> by, NodeList<Expression> declassifies, NodeList<Expression> erases, NodeList<Expression> expressions, NodeList<Expression> newObjects) {
        this(null, kind, name, by, declassifies, erases, expressions, newObjects);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlInfFlowClause(TokenRange tokenRange, JmlClauseKind kind, SimpleName name, NodeList<Expression> by, NodeList<Expression> declassifies, NodeList<Expression> erases, NodeList<Expression> expressions, NodeList<Expression> newObjects) {
        super(tokenRange, name);
        setKind(kind);
        setBy(by);
        setDeclassifies(declassifies);
        setErases(erases);
        setExpressions(expressions);
        setNewObjects(newObjects);
        customInitialization();
    }

    public JmlInfFlowClause(TokenRange range, JavaToken begin, SimpleName name, NodeList<Expression> determined, NodeList<Expression> by, NodeList<Expression> declassifies, NodeList<Expression> erases, NodeList<Expression> newObjects) {
        this(range, JmlClauseKind.getKindByToken(begin), name, determined, by, declassifies, erases, newObjects);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlClauseKind getKind() {
        return kind;
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
    public NodeList<Expression> getBy() {
        return by;
    }

    @com.github.javaparser.ast.key.IgnoreLexPrinting()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public @NonNull() NodeList<Expression> by() {
        return Objects.requireNonNull(by);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlInfFlowClause setBy(final @NonNull() NodeList<Expression> by) {
        assertNotNull(by);
        if (by == this.by) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.BY, this.by, by);
        if (this.by != null)
            this.by.setParentNode(null);
        this.by = by;
        setAsParentNodeOf(by);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Expression> getDeclassifies() {
        return declassifies;
    }

    @com.github.javaparser.ast.key.IgnoreLexPrinting()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public @NonNull() NodeList<Expression> declassifies() {
        return Objects.requireNonNull(declassifies);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlInfFlowClause setDeclassifies(final @NonNull() NodeList<Expression> declassifies) {
        assertNotNull(declassifies);
        if (declassifies == this.declassifies) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.DECLASSIFIES, this.declassifies, declassifies);
        if (this.declassifies != null)
            this.declassifies.setParentNode(null);
        this.declassifies = declassifies;
        setAsParentNodeOf(declassifies);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Expression> getErases() {
        return erases;
    }

    @com.github.javaparser.ast.key.IgnoreLexPrinting()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public @NonNull() NodeList<Expression> erases() {
        return Objects.requireNonNull(erases);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlInfFlowClause setErases(final @NonNull() NodeList<Expression> erases) {
        assertNotNull(erases);
        if (erases == this.erases) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.ERASES, this.erases, erases);
        if (this.erases != null)
            this.erases.setParentNode(null);
        this.erases = erases;
        setAsParentNodeOf(erases);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Expression> getExpressions() {
        return expressions;
    }

    @com.github.javaparser.ast.key.IgnoreLexPrinting()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public @NonNull() NodeList<Expression> expressions() {
        return Objects.requireNonNull(expressions);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlInfFlowClause setExpressions(final @NonNull() NodeList<Expression> expressions) {
        assertNotNull(expressions);
        if (expressions == this.expressions) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.EXPRESSIONS, this.expressions, expressions);
        if (this.expressions != null)
            this.expressions.setParentNode(null);
        this.expressions = expressions;
        setAsParentNodeOf(expressions);
        return this;
    }

    @com.github.javaparser.ast.key.IgnoreLexPrinting()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public @NonNull() JmlClauseKind kind() {
        return Objects.requireNonNull(kind);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlInfFlowClause setKind(final @NonNull() JmlClauseKind kind) {
        assertNotNull(kind);
        if (kind == this.kind) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.KIND, this.kind, kind);
        this.kind = kind;
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Expression> getNewObjects() {
        return newObjects;
    }

    @com.github.javaparser.ast.key.IgnoreLexPrinting()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public @NonNull() NodeList<Expression> newObjects() {
        return Objects.requireNonNull(newObjects);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlInfFlowClause setNewObjects(final @NonNull() NodeList<Expression> newObjects) {
        assertNotNull(newObjects);
        if (newObjects == this.newObjects) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.NEW_OBJECTS, this.newObjects, newObjects);
        if (this.newObjects != null)
            this.newObjects.setParentNode(null);
        this.newObjects = newObjects;
        setAsParentNodeOf(newObjects);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null) {
            return false;
        }
        for (int i = 0; i < by.size(); i++) {
            if (by.get(i) == node) {
                by.remove(i);
                return true;
            }
        }
        for (int i = 0; i < declassifies.size(); i++) {
            if (declassifies.get(i) == node) {
                declassifies.remove(i);
                return true;
            }
        }
        for (int i = 0; i < erases.size(); i++) {
            if (erases.get(i) == node) {
                erases.remove(i);
                return true;
            }
        }
        for (int i = 0; i < expressions.size(); i++) {
            if (expressions.get(i) == node) {
                expressions.remove(i);
                return true;
            }
        }
        for (int i = 0; i < newObjects.size(); i++) {
            if (newObjects.get(i) == node) {
                newObjects.remove(i);
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
        for (int i = 0; i < by.size(); i++) {
            if (by.get(i) == node) {
                by.set(i, (Expression) replacementNode);
                return true;
            }
        }
        for (int i = 0; i < declassifies.size(); i++) {
            if (declassifies.get(i) == node) {
                declassifies.set(i, (Expression) replacementNode);
                return true;
            }
        }
        for (int i = 0; i < erases.size(); i++) {
            if (erases.get(i) == node) {
                erases.set(i, (Expression) replacementNode);
                return true;
            }
        }
        for (int i = 0; i < expressions.size(); i++) {
            if (expressions.get(i) == node) {
                expressions.set(i, (Expression) replacementNode);
                return true;
            }
        }
        for (int i = 0; i < newObjects.size(); i++) {
            if (newObjects.get(i) == node) {
                newObjects.set(i, (Expression) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlInfFlowClause clone() {
        return (JmlInfFlowClause) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlInfFlowClauseMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlInfFlowClauseMetaModel;
    }
}
