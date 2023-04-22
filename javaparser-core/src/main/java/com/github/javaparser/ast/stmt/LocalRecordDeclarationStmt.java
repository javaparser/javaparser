/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.RecordDeclaration;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.LocalRecordDeclarationStmtMetaModel;
import java.util.Optional;
import java.util.function.Consumer;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * <h1>A record declaration inside a method.</h1>
 *
 * @author Roger Howell
 * @see RecordDeclaration
 */
public class LocalRecordDeclarationStmt extends Statement {

    private RecordDeclaration recordDeclaration;

    public LocalRecordDeclarationStmt() {
        this(null, new RecordDeclaration());
    }

    @AllFieldsConstructor
    public LocalRecordDeclarationStmt(final RecordDeclaration recordDeclaration) {
        this(null, recordDeclaration);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public LocalRecordDeclarationStmt(TokenRange tokenRange, RecordDeclaration recordDeclaration) {
        super(tokenRange);
        setRecordDeclaration(recordDeclaration);
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
    public RecordDeclaration getRecordDeclaration() {
        return recordDeclaration;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public LocalRecordDeclarationStmt setRecordDeclaration(final RecordDeclaration recordDeclaration) {
        assertNotNull(recordDeclaration);
        if (recordDeclaration == this.recordDeclaration) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.RECORD_DECLARATION, this.recordDeclaration, recordDeclaration);
        if (this.recordDeclaration != null)
            this.recordDeclaration.setParentNode(null);
        this.recordDeclaration = recordDeclaration;
        setAsParentNodeOf(recordDeclaration);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public LocalRecordDeclarationStmt clone() {
        return (LocalRecordDeclarationStmt) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public LocalRecordDeclarationStmtMetaModel getMetaModel() {
        return JavaParserMetaModel.localRecordDeclarationStmtMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null) {
            return false;
        }
        if (node == recordDeclaration) {
            setRecordDeclaration((RecordDeclaration) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isLocalRecordDeclarationStmt() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public LocalRecordDeclarationStmt asLocalRecordDeclarationStmt() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifLocalRecordDeclarationStmt(Consumer<LocalRecordDeclarationStmt> action) {
        action.accept(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<LocalRecordDeclarationStmt> toLocalRecordDeclarationStmt() {
        return Optional.of(this);
    }
}
