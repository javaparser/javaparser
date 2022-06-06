/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2021 The JavaParser Team.
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
public enum ResolvedPrimitiveType implements ResolvedType {


    BYTE("byte", Byte.class.getCanonicalName(), Collections.emptyList()),
    SHORT("short", Short.class.getCanonicalName(), Collections.singletonList(BYTE)),
    CHAR("char", Character.class.getCanonicalName(), Collections.emptyList()),
    INT("int", Integer.class.getCanonicalName(), Arrays.asList(BYTE, SHORT, CHAR)),
    LONG("long", Long.class.getCanonicalName(), Arrays.asList(BYTE, SHORT, INT, CHAR)),
    BOOLEAN("boolean", Boolean.class.getCanonicalName(), Collections.emptyList()),
    FLOAT("float", Float.class.getCanonicalName(), Arrays.asList(LONG, INT, SHORT, BYTE, CHAR)),
    DOUBLE("double", Double.class.getCanonicalName(), Arrays.asList(FLOAT, LONG, INT, SHORT, BYTE, CHAR));

    ///
    /// Fields
    ///

    private String name;
    private String boxTypeQName;
    private List<ResolvedPrimitiveType> promotionTypes;

    ResolvedPrimitiveType(String name, String boxTypeQName, List<ResolvedPrimitiveType> promotionTypes) {
        this.name = name;
        this.boxTypeQName = boxTypeQName;
        this.promotionTypes = promotionTypes;
    }

    public static ResolvedType byName(String name) {
        name = name.toLowerCase();
        for (ResolvedPrimitiveType ptu : values()) {
            if (ptu.describe().equals(name)) {
                return ptu;
            }
        }
        throw new IllegalArgumentException("Name " + name);
    }
    
    /*
     * Returns an array containing all numeric types
     */
    public static ResolvedPrimitiveType[] getNumericPrimitiveTypes() {
        return new ResolvedPrimitiveType[] {BYTE,SHORT,CHAR,INT,LONG,FLOAT,DOUBLE};
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
        } else {
            return other.isConstraint() && this.isAssignableBy(other.asConstraintType().getBound());
        }
    }

    public String getBoxTypeQName() {
        return boxTypeQName;
    }

    public boolean isNumeric() {
        return this != BOOLEAN;
    }
    
    /**
     * Is this a boolean type?
     */
    public boolean isBoolean() {
        return this == BOOLEAN;
    }
    
    /*
     * Binary primitive promotion (see https://docs.oracle.com/javase/specs/jls/se7/html/jls-5.html#jls-5.6.2)
     * If any operand is of a reference type, it is subjected to unboxing conversion (§5.1.8).
     */
    public ResolvedPrimitiveType bnp(ResolvedPrimitiveType other) {
        // If either operand is of type double, the other is converted to double.
        if (this == ResolvedPrimitiveType.DOUBLE || other == ResolvedPrimitiveType.DOUBLE) {
            return ResolvedPrimitiveType.DOUBLE;
        // Otherwise, if either operand is of type float, the other is converted to float.
        } else if (this == ResolvedPrimitiveType.FLOAT || other == ResolvedPrimitiveType.FLOAT) {
            return ResolvedPrimitiveType.FLOAT;
        // Otherwise, if either operand is of type long, the other is converted to long.
        } else if (this == ResolvedPrimitiveType.LONG || other == ResolvedPrimitiveType.LONG) {
            return ResolvedPrimitiveType.LONG;
        }
        // Otherwise, both operands are converted to type int.
        return ResolvedPrimitiveType.INT;
    }
    
    /*
     * Unary primitive promotion (see https://docs.oracle.com/javase/specs/jls/se9/html/jls-5.html#jls-5.6.1)
     */
    public static ResolvedType unp(ResolvedType type) {
        boolean isUnboxable = type.isReferenceType() && type.asReferenceType().isUnboxable();
        // If the operand is of compile-time type Byte, Short, Character, or Integer, it is subjected to unboxing conversion (§5.1.8). 
        // The result is then promoted to a value of type int by a widening primitive conversion (§5.1.2) or an identity conversion (§5.1.1).
        if (isUnboxable && type.asReferenceType().toUnboxedType().get().in(new ResolvedPrimitiveType[] {ResolvedPrimitiveType.BYTE, ResolvedPrimitiveType.SHORT, ResolvedPrimitiveType.CHAR, ResolvedPrimitiveType.INT})) {
            return ResolvedPrimitiveType.INT;
        }
        // Otherwise, if the operand is of compile-time type Long, Float, or Double, it is subjected to unboxing conversion (§5.1.8).
        if (isUnboxable && type.asReferenceType().toUnboxedType().get().in(new ResolvedPrimitiveType[] {ResolvedPrimitiveType.LONG, ResolvedPrimitiveType.FLOAT, ResolvedPrimitiveType.DOUBLE})) {
            return type.asReferenceType().toUnboxedType().get();
        }
        // Otherwise, if the operand is of compile-time type byte, short, or char, it is promoted to a value of type int by a widening primitive conversion (§5.1.2).
        if (type.isPrimitive() && type.asPrimitive().in(new ResolvedPrimitiveType[] {ResolvedPrimitiveType.BYTE, ResolvedPrimitiveType.CHAR, ResolvedPrimitiveType.SHORT})) {
            return ResolvedPrimitiveType.INT;
        }
        // Otherwise, a unary numeric operand remains as is and is not converted.
        return type;
    }
    
    /*
     * Verify if the ResolvedPrimitiveType is in the list of ResolvedPrimitiveType
     */
    public boolean in(ResolvedPrimitiveType... types) {
        return Arrays.stream(types).anyMatch(type -> this == type); 
    }
    
}
