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

import static com.github.javaparser.Position.pos;

import java.util.EnumSet;
import java.util.List;

import com.github.javaparser.Range;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * @author Julio Vilmar Gesser
 */
public final class AnnotationDeclaration extends TypeDeclaration {

    public AnnotationDeclaration() {
    }

    public AnnotationDeclaration(EnumSet<Modifier> modifiers, String name) {
        super(modifiers, name);
    }

    public AnnotationDeclaration(EnumSet<Modifier> modifiers, List<AnnotationExpr> annotations, String name,
                                 List<BodyDeclaration> members) {
        super(annotations, modifiers, name, members);
    }

    /**
     * @deprecated prefer using Range objects.
     */
    @Deprecated
    public AnnotationDeclaration(int beginLine, int beginColumn, int endLine, int endColumn,
                                 EnumSet<Modifier> modifiers, List<AnnotationExpr> annotations, String name,
                                 List<BodyDeclaration> members) {
        this(new Range(pos(beginLine, beginColumn), pos(endLine, endColumn)), modifiers, annotations, name, members);
    }
    
    public AnnotationDeclaration(Range range, EnumSet<Modifier> modifiers, List<AnnotationExpr> annotations,
                                 String name, List<BodyDeclaration> members) {
        super(range, annotations, modifiers, name, members);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }
}
