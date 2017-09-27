/*
 * Copyright 2016 Federico Tomassetti
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
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
