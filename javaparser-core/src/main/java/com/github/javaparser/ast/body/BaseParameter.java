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
 
package com.github.javaparser.ast.body;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeWithModifiers;
import com.github.javaparser.ast.expr.AnnotationExpr;

import javax.lang.model.element.Modifier;
import java.util.EnumSet;
import java.util.List;
import java.util.Set;

public abstract class BaseParameter extends Node implements NodeWithModifiers {
    private ModifiersSet modifiers = new ModifiersSet();

    private List<AnnotationExpr> annotations;
    
    private VariableDeclaratorId id;
    
    public BaseParameter() {
    }
    
    public BaseParameter(VariableDeclaratorId id) {
        setId(id);
	}

	public BaseParameter(int modifiers, VariableDeclaratorId id) {
        setModifiers(modifiers);
        setId(id);
	}
	
	public BaseParameter(int modifiers, List<AnnotationExpr> annotations, VariableDeclaratorId id) {
        setModifiers(modifiers);
        setAnnotations(annotations);
        setId(id);
	}

	public BaseParameter(int beginLine, int beginColumn, int endLine, int endColumn, int modifiers, List<AnnotationExpr> annotations, VariableDeclaratorId id) {
	    super(beginLine, beginColumn, endLine, endColumn);
        setModifiers(modifiers);
        setAnnotations(annotations);
        setId(id);
	}

    public List<AnnotationExpr> getAnnotations() {
        return annotations;
    }

    public VariableDeclaratorId getId() {
        return id;
    }

    /**
     * Return the modifiers of this member declaration.
     *
     * @see ModifierUtils
     * @return modifiers
     * @deprecated please use getModifiersSet instead
     */
    @Override
    @Deprecated
    public int getModifiers() {
        return ModifierUtils.toInt(modifiers);
    }

    /**
     * Return the modifiers of this member declaration.
     *
     * @see ModifierUtils
     * @return modifiers
     */
    @Override
    public ModifiersSet getModifiersSet() {
        return modifiers;
    }

    public void setAnnotations(List<AnnotationExpr> annotations) {
        this.annotations = annotations;
        setAsParentNodeOf(this.annotations);
    }

    public void setId(VariableDeclaratorId id) {
        this.id = id;
        setAsParentNodeOf(this.id);
    }

    public final void setModifiers(ModifiersSet modifiers) {
        this.modifiers = modifiers;
    }

    public final void setModifiers(int modifiers) {
        this.modifiers = ModifierUtils.toSet(modifiers);
    }

}
