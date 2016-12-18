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

package com.github.javaparser.ast.type;

import com.github.javaparser.Range;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.HashMap;

/**
 * @author Julio Vilmar Gesser
 */
public final class PrimitiveType extends Type implements NodeWithAnnotations<PrimitiveType> {

    public static final PrimitiveType BYTE_TYPE = new PrimitiveType(Primitive.BYTE);

    public static final PrimitiveType SHORT_TYPE = new PrimitiveType(Primitive.SHORT);

    public static final PrimitiveType INT_TYPE = new PrimitiveType(Primitive.INT);

    public static final PrimitiveType LONG_TYPE = new PrimitiveType(Primitive.LONG);

    public static final PrimitiveType FLOAT_TYPE = new PrimitiveType(Primitive.FLOAT);

    public static final PrimitiveType DOUBLE_TYPE = new PrimitiveType(Primitive.DOUBLE);

    public static final PrimitiveType BOOLEAN_TYPE = new PrimitiveType(Primitive.BOOLEAN);

    public static final PrimitiveType CHAR_TYPE = new PrimitiveType(Primitive.CHAR);

    public enum Primitive {
        BOOLEAN("Boolean"),
        CHAR("Character"),
        BYTE("Byte"),
        SHORT("Short"),
        INT("Integer"),
        LONG("Long"),
        FLOAT("Float"),
        DOUBLE("Double");

        final String nameOfBoxedType;
        private String codeRepresentation;

        public ClassOrInterfaceType toBoxedType() {
            return new ClassOrInterfaceType(nameOfBoxedType);
        }

        public String asString() {
            return codeRepresentation;
        }

        Primitive(String nameOfBoxedType) {
            this.nameOfBoxedType = nameOfBoxedType;
            this.codeRepresentation = name().toLowerCase();
        }
    }

    static final HashMap<String, Primitive> unboxMap = new HashMap<>();

    static {
        for (Primitive unboxedType : Primitive.values()) {
            unboxMap.put(unboxedType.nameOfBoxedType, unboxedType);
        }
    }

    private Primitive type;

    public PrimitiveType() {
        this(null, Primitive.INT);
    }

    public PrimitiveType(final Primitive type) {
        this(null, type);
    }

    public PrimitiveType(Range range, final Primitive type) {
        super(range, new NodeList<>());
        setType(type);
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    public Primitive getType() {
        return type;
    }

    public ClassOrInterfaceType toBoxedType() {
        return type.toBoxedType();
    }

    public PrimitiveType setType(final Primitive type) {
        notifyPropertyChange(ObservableProperty.TYPE, this.type, type);
        this.type = type;
        return this;
    }

    public String asString() {
        return type.asString();
    }

    @Override
    public PrimitiveType setAnnotations(NodeList<AnnotationExpr> annotations) {
        return (PrimitiveType) super.setAnnotations(annotations);
    }
}
