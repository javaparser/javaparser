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
import static com.github.javaparser.ast.internal.Utils.ensureNotNull;

import java.util.EnumSet;
import java.util.List;

import com.github.javaparser.Range;
import com.github.javaparser.ast.NamedNode;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeWithModifiers;
import com.github.javaparser.ast.expr.AnnotationExpr;

public abstract class BaseParameter
    extends Node
    implements AnnotableNode, NamedNode, NodeWithModifiers
{
    private EnumSet<Modifier> modifiers = EnumSet.noneOf(Modifier.class);

    private List<AnnotationExpr> annotations;
    
    private VariableDeclaratorId id;
    
    public BaseParameter() {
    }
    
    public BaseParameter(VariableDeclaratorId id) {
        setId(id);
	}

    public BaseParameter(EnumSet<Modifier> modifiers, VariableDeclaratorId id) {
        setModifiers(modifiers);
        setId(id);
	}
	
    public BaseParameter(EnumSet<Modifier> modifiers, List<AnnotationExpr> annotations, VariableDeclaratorId id) {
        setModifiers(modifiers);
        setAnnotations(annotations);
        setId(id);
	}

    /**
     * @deprecated prefer using Range objects.
     */
    @Deprecated
    public BaseParameter(int beginLine, int beginColumn, int endLine, int endColumn, EnumSet<Modifier> modifiers,
                         List<AnnotationExpr> annotations, VariableDeclaratorId id) {
        this(new Range(pos(beginLine, beginColumn), pos(endLine, endColumn)), modifiers, annotations, id);
    }

    public BaseParameter(final Range range, EnumSet<Modifier> modifiers, List<AnnotationExpr> annotations,
                         VariableDeclaratorId id) {
	    super(range);
        setModifiers(modifiers);
        setAnnotations(annotations);
        setId(id);
	}

    /**
     * @return the list returned could be immutable (in that case it will be empty)
     */
    @Override
    public List<AnnotationExpr> getAnnotations() {
        annotations = ensureNotNull(annotations);
        return annotations;
    }

    public VariableDeclaratorId getId() {
        return id;
    }

    @Override
    public String getName() {
        return getId().getName();
    }

    /**
     * Return the modifiers of this parameter declaration.
     * 
     * @see ModifierSet
     * @return modifiers
     */
    @Override
    public EnumSet<Modifier> getModifiers() {
        return modifiers;
    }

    /**
     * @param annotations a null value is currently treated as an empty list. This behavior could change
     *                    in the future, so please avoid passing null
     */
    public void setAnnotations(List<AnnotationExpr> annotations) {
        this.annotations = annotations;
        setAsParentNodeOf(this.annotations);
    }

    public void setId(VariableDeclaratorId id) {
        this.id = id;
        setAsParentNodeOf(this.id);
    }

    public void setModifiers(EnumSet<Modifier> modifiers) {
        this.modifiers = modifiers;
    }
}
