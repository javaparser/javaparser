/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2015 The JavaParser Team.
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
 
package com.github.javaparser.ast.type;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.AnnotationExpr;

import java.util.List;

/**
 * @author Julio Vilmar Gesser
 */
public abstract class Type extends Node {

    private List<AnnotationExpr> annotations;

    public Type() {
    }

    public Type(List<AnnotationExpr> annotation){
        this.annotations = annotation;
    }

    public Type(int beginLine, int beginColumn, int endLine, int endColumn) {
        super(beginLine, beginColumn, endLine, endColumn);
    }

    public Type(int beginLine, int beginColumn, int endLine, int endColumn, List<AnnotationExpr> annotations) {
        super(beginLine, beginColumn, endLine, endColumn);
        this.annotations = annotations;
    }

    public List<AnnotationExpr> getAnnotations() {
        return annotations;
    }

    public void setAnnotations(List<AnnotationExpr> annotations) {
        this.annotations = annotations;
    }

}
