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

package com.github.javaparser.ast.expr;

import com.github.javaparser.Range;
import com.github.javaparser.ast.nodeTypes.NodeWithName;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Julio Vilmar Gesser
 */
public abstract class AnnotationExpr extends Expression implements NodeWithName<AnnotationExpr> {

    protected Name name;

    public AnnotationExpr() {
        this(Range.UNKNOWN, new Name());
    }

    public AnnotationExpr(Name name) {
        this(Range.UNKNOWN, name);
    }
    
    public AnnotationExpr(Range range, Name name) {
        super(range);
        setName(name);
    }

    public Name getName() {
        return name;
    }

    public AnnotationExpr setName(Name name) {
        notifyPropertyChange("name", this.name, name);
        this.name = assertNotNull(name);
        setAsParentNodeOf(name);
        return this;
    }
}
