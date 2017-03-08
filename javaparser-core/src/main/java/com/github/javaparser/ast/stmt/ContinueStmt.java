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
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithOptionalLabel;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Optional;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.ContinueStmtMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

/**
 * A continue statement with an optional label;
 * <br/><code>continue brains;</code>
 * <br/><code>continue;</code>
 *
 * @author Julio Vilmar Gesser
 */
public final class ContinueStmt extends Statement implements NodeWithOptionalLabel<ContinueStmt> {

    private SimpleName label;

    public ContinueStmt() {
        this(null, null);
    }

    public ContinueStmt(final String label) {
        this(null, new SimpleName(label));
    }

    @AllFieldsConstructor
    public ContinueStmt(final SimpleName label) {
        this(null, label);
    }

    public ContinueStmt(Range range, final SimpleName label) {
        super(range);
        this.label = label;
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
    public Optional<SimpleName> getLabel() {
        return Optional.ofNullable(label);
    }

    /**
     * Sets the label
     *
     * @param label the label, can be null
     * @return this, the ContinueStmt
     */
    @Override
    public ContinueStmt setLabel(final SimpleName label) {
        notifyPropertyChange(ObservableProperty.LABEL, this.label, label);
        if (this.label != null)
            this.label.setParentNode(null);
        this.label = label;
        setAsParentNodeOf(label);
        return this;
    }

    @Override
    public boolean remove(Node node) {
        if (node == null)
            return false;
        if (label != null) {
            if (node == label) {
                removeLabel();
                return true;
            }
        }
        return super.remove(node);
    }

    public ContinueStmt removeLabel() {
        return setLabel((SimpleName) null);
    }

    @Override
    public ContinueStmt clone() {
        return (ContinueStmt) accept(new CloneVisitor(), null);
    }

    @Override
    public ContinueStmtMetaModel getMetaModel() {
        return JavaParserMetaModel.continueStmtMetaModel;
    }
}
