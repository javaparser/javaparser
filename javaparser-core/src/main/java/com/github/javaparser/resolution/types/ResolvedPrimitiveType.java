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

package com.github.javaparser.resolution.types;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

/**
 * @author Federico Tomassetti
 */
public class ResolvedPrimitiveType implements ResolvedType {

    ///
    /// Constants
    ///

    public static final ResolvedPrimitiveType BYTE = new ResolvedPrimitiveType("byte",
            Byte.class.getCanonicalName(), Collections.emptyList());
    public static final ResolvedPrimitiveType SHORT = new ResolvedPrimitiveType("short",
            Short.class.getCanonicalName(), Collections.singletonList(BYTE));
    public static final ResolvedPrimitiveType CHAR = new ResolvedPrimitiveType("char",
            Character.class.getCanonicalName(), Collections.emptyList());
    public static final ResolvedPrimitiveType INT = new ResolvedPrimitiveType("int",
            Integer.class.getCanonicalName(), Arrays.asList(BYTE, SHORT, CHAR));
    public static final ResolvedPrimitiveType LONG = new ResolvedPrimitiveType("long",
            Long.class.getCanonicalName(), Arrays.asList(BYTE, SHORT, INT, CHAR));
    public static final ResolvedPrimitiveType BOOLEAN = new ResolvedPrimitiveType("boolean",
            Boolean.class.getCanonicalName(), Collections.emptyList());
    public static final ResolvedPrimitiveType FLOAT = new ResolvedPrimitiveType("float",
            Float.class.getCanonicalName(), Arrays.asList(LONG, INT, SHORT, BYTE, CHAR));
    public static final ResolvedPrimitiveType DOUBLE = new ResolvedPrimitiveType("double",
            Double.class.getCanonicalName(), Arrays.asList(FLOAT, LONG, INT, SHORT, BYTE, CHAR));
    public static final List<ResolvedPrimitiveType> ALL = Arrays.asList(
            INT, BOOLEAN, LONG, CHAR, FLOAT, DOUBLE, SHORT, BYTE);

    ///
    /// Fields
    ///

    private String name;
    private String boxTypeQName;
    private List<ResolvedPrimitiveType> promotionTypes;

    private ResolvedPrimitiveType(String name, String boxTypeQName, List<ResolvedPrimitiveType> promotionTypes) {
        this.name = name;
        this.boxTypeQName = boxTypeQName;
        this.promotionTypes = promotionTypes;
    }

    public static ResolvedType byName(String name) {
        name = name.toLowerCase();
        for (ResolvedPrimitiveType ptu : ALL) {
            if (ptu.describe().equals(name)) {
                return ptu;
            }
        }
        throw new IllegalArgumentException("Name " + name);
    }

    @Override
    public String toString() {
        return "PrimitiveTypeUsage{" +
                "name='" + name + '\'' +
                '}';
    }

    public ResolvedPrimitiveType asPrimitive() {
        return this;
    }

    @Override
    public boolean isArray() {
        return false;
    }

    @Override
    public boolean isPrimitive() {
        return true;
    }

    @Override
    public boolean isReferenceType() {
        return false;
    }

    @Override
    public String describe() {
        return name;
    }

    @Override
    public boolean isTypeVariable() {
        return false;
    }

    @Override
    public boolean isAssignableBy(ResolvedType other) {
        if (other.isPrimitive()) {
            return this == other || promotionTypes.contains(other);
        } else if (other.isReferenceType()) {
            if (other.asReferenceType().getQualifiedName().equals(boxTypeQName)) {
                return true;
            }
            for (ResolvedPrimitiveType promotion : promotionTypes) {
                if (other.asReferenceType().getQualifiedName().equals(promotion.boxTypeQName)) {
                    return true;
                }
            }
            return false;
        } else if (other.isConstraint()){
            return this.isAssignableBy(other.asConstraintType().getBound());
        } else {
            return false;
        }
    }

    public String getBoxTypeQName() {
        return boxTypeQName;
    }

}
