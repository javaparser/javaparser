/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */
package com.github.javaparser.ast.stmt;

import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.expr.BooleanLiteralExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.nodeTypes.NodeWithCondition;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Optional;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.DerivedProperty;
import com.github.javaparser.metamodel.IfStmtMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import javax.annotation.Generated;
import com.github.javaparser.TokenRange;
import com.github.javaparser.metamodel.OptionalProperty;
import java.util.function.Consumer;

/**
 * An if-then-else statement. The else is optional.
 * <br/>In <code>if(a==5) hurray() else boo();</code> the condition is a==5,
 * hurray() is the thenStmt, and boo() is the elseStmt.
 *
 * @author Julio Vilmar Gesser
 */
public final class IfStmt extends Statement implements NodeWithCondition<IfStmt> {

    private Expression condition;

    private Statement thenStmt;

    @OptionalProperty
    private Statement elseStmt;

    public IfStmt() {
        this(null, new BooleanLiteralExpr(), new ReturnStmt(), null);
    }

    @AllFieldsConstructor
    public IfStmt(final Expression condition, final Statement thenStmt, final Statement elseStmt) {
        this(null, condition, thenStmt, elseStmt);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public IfStmt(TokenRange tokenRange, Expression condition, Statement thenStmt, Statement elseStmt) {
        super(tokenRange);
        setCondition(condition);
        setThenStmt(thenStmt);
        setElseStmt(elseStmt);
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
    public Expression getCondition() {
        return condition;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<Statement> getElseStmt() {
        return Optional.ofNullable(elseStmt);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Statement getThenStmt() {
        return thenStmt;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public IfStmt setCondition(final Expression condition) {
        assertNotNull(condition);
        if (condition == this.condition) {
            return (IfStmt) this;
        }
        notifyPropertyChange(ObservableProperty.CONDITION, this.condition, condition);
        if (this.condition != null)
            this.condition.setParentNode(null);
        this.condition = condition;
        setAsParentNodeOf(condition);
        return this;
    }

    /**
     * Sets the elseStmt
     *
     * @param elseStmt the elseStmt, can be null
     * @return this, the IfStmt
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public IfStmt setElseStmt(final Statement elseStmt) {
        if (elseStmt == this.elseStmt) {
            return (IfStmt) this;
        }
        notifyPropertyChange(ObservableProperty.ELSE_STMT, this.elseStmt, elseStmt);
        if (this.elseStmt != null)
            this.elseStmt.setParentNode(null);
        this.elseStmt = elseStmt;
        setAsParentNodeOf(elseStmt);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public IfStmt setThenStmt(final Statement thenStmt) {
        assertNotNull(thenStmt);
        if (thenStmt == this.thenStmt) {
            return (IfStmt) this;
        }
        notifyPropertyChange(ObservableProperty.THEN_STMT, this.thenStmt, thenStmt);
        if (this.thenStmt != null)
            this.thenStmt.setParentNode(null);
        this.thenStmt = thenStmt;
        setAsParentNodeOf(thenStmt);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        if (elseStmt != null) {
            if (node == elseStmt) {
                removeElseStmt();
                return true;
            }
        }
        return super.remove(node);
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public IfStmt removeElseStmt() {
        return setElseStmt((Statement) null);
    }

    /**
     * This method returns true if the then branch (which should be always present) is a block statement.
     */
    @DerivedProperty
    public boolean hasThenBlock() {
        return thenStmt instanceof BlockStmt;
    }

    /**
     * This method returns true if the If Statement has an else branch and that branch is a block statement.
     */
    @DerivedProperty
    public boolean hasElseBlock() {
        return elseStmt instanceof BlockStmt;
    }

    /**
     * This method returns true if the If Statement has an else branch and that branch is another If Statement.
     */
    @DerivedProperty
    public boolean hasCascadingIfStmt() {
        return elseStmt instanceof IfStmt;
    }

    /**
     * This method returns true if the If Statement has an else branch.
     */
    @DerivedProperty
    public boolean hasElseBranch() {
        return elseStmt != null;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public IfStmt clone() {
        return (IfStmt) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public IfStmtMetaModel getMetaModel() {
        return JavaParserMetaModel.ifStmtMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        if (node == condition) {
            setCondition((Expression) replacementNode);
            return true;
        }
        if (elseStmt != null) {
            if (node == elseStmt) {
                setElseStmt((Statement) replacementNode);
                return true;
            }
        }
        if (node == thenStmt) {
            setThenStmt((Statement) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isIfStmt() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public IfStmt asIfStmt() {
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifIfStmt(Consumer<IfStmt> action) {
        action.accept(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<IfStmt> toIfStmt() {
        return Optional.of(this);
    }
}
