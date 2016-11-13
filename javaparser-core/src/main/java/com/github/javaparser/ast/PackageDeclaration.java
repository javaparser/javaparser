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
 
package com.github.javaparser.ast;

import com.github.javaparser.Range;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.utils.Utils;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.List;

/**
 * <p>
 * This class represents the package declaration. The package declaration is
 * optional for the {@link CompilationUnit}.
 * </p>
 * The PackageDeclaration is constructed following the syntax:<br>
 * <pre>
 * {@code
 * PackageDeclaration ::= ( }{@link AnnotationExpr}{@code )* "package" }{@link NameExpr}{@code ) ";"
 * }
 * </pre>
 * @author Julio Vilmar Gesser
 */
public final class PackageDeclaration extends Node implements NodeWithAnnotations<PackageDeclaration> {

    private List<AnnotationExpr> annotationsList;

    private NameExpr name;

    public PackageDeclaration() {
    }

    public PackageDeclaration(NameExpr name) {
        setName(name);
    }

    public PackageDeclaration(List<AnnotationExpr> annotationsList, NameExpr name) {
        setAnnotationsList(annotationsList);
        setName(name);
    }

    public PackageDeclaration(Range range, List<AnnotationExpr> annotationsList, NameExpr name) {
        super(range);
        setAnnotationsList(annotationsList);
        setName(name);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    /**
     * Retrieves the list of annotationsList declared before the package
     * declaration. Return <code>null</code> if there are no annotationsList.
     * 
     * @return list of annotationsList or <code>null</code>
     */
    public List<AnnotationExpr> getAnnotationsList() {
        annotationsList = Utils.ensureNotNull(annotationsList);
        return annotationsList;
    }

    /**
     * Return the name expression of the package.
     *
     * @return the name of the package
     */
    public NameExpr getName() {
        return name;
    }

    /**
     * Get full package name.
     */
    public String getPackageName() {
        return name.toString();
    }

    /**
     * @param annotationsList
     *            the annotationsList to set
     */
    public PackageDeclaration setAnnotationsList(List<AnnotationExpr> annotationsList) {
        this.annotationsList = annotationsList;
        setAsParentNodeOf(this.annotationsList);
        return this;
    }

    /**
     * Sets the name of this package declaration.
     * 
     * @param name
     *            the name to set
     */
    public PackageDeclaration setName(NameExpr name) {
        this.name = name;
        setAsParentNodeOf(this.name);
        return this;
    }

}
