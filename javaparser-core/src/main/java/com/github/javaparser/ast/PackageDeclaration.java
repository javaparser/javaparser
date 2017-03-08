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
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.nodeTypes.NodeWithName;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Arrays;
import java.util.List;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.PackageDeclarationMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

/**
 * A package declaration.
 * <br/><code>package com.github.javaparser.ast;</code>
 * <br/><code>@Wonderful package anything.can.be.annotated.nowadays;</code>
 *
 * @author Julio Vilmar Gesser
 */
public final class PackageDeclaration extends Node implements NodeWithAnnotations<PackageDeclaration>, NodeWithName<PackageDeclaration> {

    private NodeList<AnnotationExpr> annotations = new NodeList<>();

    private Name name;

    public PackageDeclaration() {
        this(null, new NodeList<>(), new Name());
    }

    public PackageDeclaration(Name name) {
        this(null, new NodeList<>(), name);
    }

    @AllFieldsConstructor
    public PackageDeclaration(NodeList<AnnotationExpr> annotations, Name name) {
        this(null, annotations, name);
    }

    public PackageDeclaration(Range range, NodeList<AnnotationExpr> annotations, Name name) {
        super(range);
        setAnnotations(annotations);
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
     * Retrieves the list of annotations declared before the package
     * declaration. Return <code>null</code> if there are no annotations.
     *
     * @return list of annotations or <code>null</code>
     */
    @Override
    public NodeList<AnnotationExpr> getAnnotations() {
        return annotations;
    }

    /**
     * Return the name expression of the package.
     *
     * @return the name of the package
     */
    @Override
    public Name getName() {
        return name;
    }

    /**
     * @param annotations the annotations to set
     */
    @Override
    public PackageDeclaration setAnnotations(final NodeList<AnnotationExpr> annotations) {
        assertNotNull(annotations);
        notifyPropertyChange(ObservableProperty.ANNOTATIONS, this.annotations, annotations);
        if (this.annotations != null)
            this.annotations.setParentNode(null);
        this.annotations = annotations;
        setAsParentNodeOf(annotations);
        return this;
    }

    /**
     * Sets the name of this package declaration.
     *
     * @param name the name to set
     */
    @Override
    public PackageDeclaration setName(final Name name) {
        assertNotNull(name);
        notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        if (this.name != null)
            this.name.setParentNode(null);
        this.name = name;
        setAsParentNodeOf(name);
        return this;
    }

    @Override
    public List<NodeList<?>> getNodeLists() {
        return Arrays.asList(getAnnotations());
    }

    @Override
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < annotations.size(); i++) {
            if (annotations.get(i) == node) {
                annotations.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Override
    public PackageDeclaration clone() {
        return (PackageDeclaration) accept(new CloneVisitor(), null);
    }

    @Override
    public PackageDeclarationMetaModel getMetaModel() {
        return JavaParserMetaModel.packageDeclarationMetaModel;
    }
}
