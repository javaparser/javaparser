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
 
package com.github.javaparser.ast.body;

import java.util.List;

import com.github.javaparser.Range;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.utils.Utils;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Julio Vilmar Gesser
 */
public abstract class BodyDeclaration<T> extends Node implements NodeWithAnnotations<T> {

    private NodeList<AnnotationExpr> annotations = new NodeList<>();

    public BodyDeclaration() {
    }

    public BodyDeclaration(NodeList<AnnotationExpr> annotations) {
    	setAnnotations(annotations);
    }

    public BodyDeclaration(Range range, NodeList<AnnotationExpr> annotations) {
        super(range);
    	setAnnotations(annotations);
    }

    @Override
    public final NodeList<AnnotationExpr> getAnnotations() {
        return annotations;
    }

    /**
     *
     * @param annotations a null value is currently treated as an empty list. This behavior could change
     *                    in the future, so please avoid passing null
     */
    @SuppressWarnings("unchecked")
    @Override
    public final T setAnnotations(NodeList<AnnotationExpr> annotations) {
        this.annotations = assertNotNull(annotations);
		setAsParentNodeOf(this.annotations);
        return (T) this;
    }
}
