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
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Optional;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.AssertStmtMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import javax.annotation.Generated;
import com.github.javaparser.TokenRange;
import com.github.javaparser.metamodel.OptionalProperty;
import java.util.function.Consumer;

/**
 * A usage of the keyword "assert"
 * <br/>In <code>assert dead : "Wasn't expecting to be dead here";</code> the check is "dead" and the message is the string.
 * @author Julio Vilmar Gesser
 */
public final class AssertStmt extends Statement {

    private Expression check;

    @OptionalProperty
    private Expression message;

    public AssertStmt() {
        this(null, new BooleanLiteralExpr(), null);
    }

    public AssertStmt(final Expression check) {
        this(null, check, null);
    }

    @AllFieldsConstructor
    public AssertStmt(final Expression check, final Expression message) {
        this(null, check, message);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public AssertStmt(TokenRange tokenRange, Expression check, Expression message) {
        super(tokenRange);
        setCheck(check);
        setMessage(message);
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
    public Expression getCheck() {
        return check;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<Expression> getMessage() {
        return Optional.ofNullable(message);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public AssertStmt setCheck(final Expression check) {
        assertNotNull(check);
        if (check == this.check) {
            return (AssertStmt) this;
        }
        notifyPropertyChange(ObservableProperty.CHECK, this.check, check);
        if (this.check != null)
            this.check.setParentNode(null);
        this.check = check;
        setAsParentNodeOf(check);
        return this;
    }

    /**
     * Sets the message
     *
     * @param message the message, can be null
     * @return this, the AssertStmt
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public AssertStmt setMessage(final Expression message) {
        if (message == this.message) {
            return (AssertStmt) this;
        }
        notifyPropertyChange(ObservableProperty.MESSAGE, this.message, message);
        if (this.message != null)
            this.message.setParentNode(null);
        this.message = message;
        setAsParentNodeOf(message);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        if (message != null) {
            if (node == message) {
                removeMessage();
                return true;
            }
        }
        return super.remove(node);
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public AssertStmt removeMessage() {
        return setMessage((Expression) null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public AssertStmt clone() {
        return (AssertStmt) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public AssertStmtMetaModel getMetaModel() {
        return JavaParserMetaModel.assertStmtMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        if (node == check) {
            setCheck((Expression) replacementNode);
            return true;
        }
        if (message != null) {
            if (node == message) {
                setMessage((Expression) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isAssertStmt() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public AssertStmt asAssertStmt() {
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifAssertStmt(Consumer<AssertStmt> action) {
        action.accept(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<AssertStmt> toAssertStmt() {
        return Optional.of(this);
    }
}
