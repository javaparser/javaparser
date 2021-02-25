/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2020 The JavaParser Team.
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

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Jmlish;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;

/**
 * A primitive type.
 * <br>{@code int}
 * <br>{@code boolean}
 * <br>{@code short}
 *
 * @author Julio Vilmar Gesser
 */
public class JmlLogicType extends Type implements Jmlish {


    public enum Primitive {
        SET("\\set"),
        SEQ("\\seq"),
        MAP("\\map"),
        BIGINT("\\bigint"),
        BIGFLOAT("\\bigfloat");

        final String descriptor;

        public String asString() {
            return descriptor;
        }

        Primitive(String descriptor) {
            this.descriptor = descriptor;
        }
    }

    private Primitive type;

    /*public JmlLogicType() {
        this(null, Primitive.BIGINT, new NodeList<>());
    }

    public JmlLogicType(final Primitive type) {
        this(null, type, new NodeList<>());
    }
*/
    @AllFieldsConstructor
    public JmlLogicType(final Primitive type, NodeList<AnnotationExpr> annotations) {
        super((TokenRange) null);
        //this(null, type, annotations);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.AcceptGenerator")
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return null;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.AcceptGenerator")
    public <A> void accept(final VoidVisitor<A> v, final A arg) {

    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Primitive getType() {
        return type;
    }

    @Override
    public String toDescriptor() {
        return type.descriptor;
    }

    @Override
    public String asString() {
        return toDescriptor();
    }

    @Override
    public ResolvedPrimitiveType resolve() {
        return getSymbolResolver().toResolvedType(this, ResolvedPrimitiveType.class);
    }
}
