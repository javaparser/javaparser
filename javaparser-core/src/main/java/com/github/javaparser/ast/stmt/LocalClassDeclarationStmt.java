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
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.LocalClassDeclarationStmtMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import javax.annotation.Generated;
import com.github.javaparser.TokenRange;

/**
 * A class declaration inside a method. 
 * Note that JavaParser wil parse interface declarations too, but these are not valid Java code.
 * <p>
 * <br/><code>class X { void m() { <b>class Y { }</b> } }</code>
 *
 * @author Julio Vilmar Gesser
 */
public final class LocalClassDeclarationStmt extends Statement {

    private ClassOrInterfaceDeclaration classDeclaration;

    public LocalClassDeclarationStmt() {
        this(null, new ClassOrInterfaceDeclaration());
    }

    @AllFieldsConstructor
    public LocalClassDeclarationStmt(final ClassOrInterfaceDeclaration classDeclaration) {
        this(null, classDeclaration);
    }

    /**This constructor is used by the parser and is considered private.*/
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public LocalClassDeclarationStmt(TokenRange tokenRange, ClassOrInterfaceDeclaration classDeclaration) {
        super(tokenRange);
        setClassDeclaration(classDeclaration);
        customInitialization();
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ClassOrInterfaceDeclaration getClassDeclaration() {
        return classDeclaration;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public LocalClassDeclarationStmt setClassDeclaration(final ClassOrInterfaceDeclaration classDeclaration) {
        assertNotNull(classDeclaration);
        if (classDeclaration == this.classDeclaration) {
            return (LocalClassDeclarationStmt) this;
        }
        notifyPropertyChange(ObservableProperty.CLASS_DECLARATION, this.classDeclaration, classDeclaration);
        if (this.classDeclaration != null)
            this.classDeclaration.setParentNode(null);
        this.classDeclaration = classDeclaration;
        setAsParentNodeOf(classDeclaration);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public LocalClassDeclarationStmt clone() {
        return (LocalClassDeclarationStmt) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public LocalClassDeclarationStmtMetaModel getMetaModel() {
        return JavaParserMetaModel.localClassDeclarationStmtMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        if (node == classDeclaration) {
            setClassDeclaration((ClassOrInterfaceDeclaration) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }
}
