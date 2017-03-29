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

import com.github.javaparser.Range;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.BooleanLiteralExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.nodeTypes.NodeWithBody;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.Optional;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.ForStmtMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

/**
 * A classic for statement.
 * <br/>In <code>for(int a=3,b==5; a<99; a++) { ... }</code> the intialization is int a=3,b=5, 
 * compare is b==5, update is a++, and the statement or block statement following it is in body.  
 *
 * @author Julio Vilmar Gesser
 */
public final class ForStmt extends Statement implements NodeWithBody<ForStmt> {

    private NodeList<Expression> initialization;

    private Expression compare;

    private NodeList<Expression> update;

    private Statement body;

    public ForStmt() {
        this(null, new NodeList<>(), new BooleanLiteralExpr(), new NodeList<>(), new ReturnStmt());
    }

    @AllFieldsConstructor
    public ForStmt(final NodeList<Expression> initialization, final Expression compare, final NodeList<Expression> update, final Statement body) {
        this(null, initialization, compare, update, body);
    }

    public ForStmt(Range range, final NodeList<Expression> initialization, final Expression compare, final NodeList<Expression> update, final Statement body) {
        super(range);
        setCompare(compare);
        setInitialization(initialization);
        setUpdate(update);
        setBody(body);
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    @Override
    public Statement getBody() {
        return body;
    }

    public Optional<Expression> getCompare() {
        return Optional.ofNullable(compare);
    }

    public NodeList<Expression> getInitialization() {
        return initialization;
    }

    public NodeList<Expression> getUpdate() {
        return update;
    }

    @Override
    public ForStmt setBody(final Statement body) {
        assertNotNull(body);
        if (body == this.body) {
            return (ForStmt) this;
        }
        notifyPropertyChange(ObservableProperty.BODY, this.body, body);
        if (this.body != null)
            this.body.setParentNode(null);
        this.body = body;
        setAsParentNodeOf(body);
        return this;
    }

    /**
     * Sets the compare
     *
     * @param compare the compare, can be null
     * @return this, the ForStmt
     */
    public ForStmt setCompare(final Expression compare) {
        if (compare == this.compare) {
            return (ForStmt) this;
        }
        notifyPropertyChange(ObservableProperty.COMPARE, this.compare, compare);
        if (this.compare != null)
            this.compare.setParentNode(null);
        this.compare = compare;
        setAsParentNodeOf(compare);
        return this;
    }

    public ForStmt setInitialization(final NodeList<Expression> initialization) {
        assertNotNull(initialization);
        if (initialization == this.initialization) {
            return (ForStmt) this;
        }
        notifyPropertyChange(ObservableProperty.INITIALIZATION, this.initialization, initialization);
        if (this.initialization != null)
            this.initialization.setParentNode(null);
        this.initialization = initialization;
        setAsParentNodeOf(initialization);
        return this;
    }

    public ForStmt setUpdate(final NodeList<Expression> update) {
        assertNotNull(update);
        if (update == this.update) {
            return (ForStmt) this;
        }
        notifyPropertyChange(ObservableProperty.UPDATE, this.update, update);
        if (this.update != null)
            this.update.setParentNode(null);
        this.update = update;
        setAsParentNodeOf(update);
        return this;
    }

    @Override
    public List<NodeList<?>> getNodeLists() {
        return Arrays.asList(getInitialization(), getUpdate());
    }

    @Override
    public boolean remove(Node node) {
        if (node == null)
            return false;
        if (compare != null) {
            if (node == compare) {
                removeCompare();
                return true;
            }
        }
        for (int i = 0; i < initialization.size(); i++) {
            if (initialization.get(i) == node) {
                initialization.remove(i);
                return true;
            }
        }
        for (int i = 0; i < update.size(); i++) {
            if (update.get(i) == node) {
                update.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    public ForStmt removeCompare() {
        return setCompare((Expression) null);
    }

    @Override
    public ForStmt clone() {
        return (ForStmt) accept(new CloneVisitor(), null);
    }

    @Override
    public ForStmtMetaModel getMetaModel() {
        return JavaParserMetaModel.forStmtMetaModel;
    }
}
