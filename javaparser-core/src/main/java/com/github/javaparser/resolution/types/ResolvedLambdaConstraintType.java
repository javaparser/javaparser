/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
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

public class ResolvedLambdaConstraintType implements ResolvedType {

    private ResolvedType bound;

    private ResolvedLambdaConstraintType(ResolvedType bound) {
        this.bound = bound;
    }

    /**
     * The bound is the type the lambda parameter was inferred to, so that is what callers are
     * shown. Rendering it as {@code "? super " + bound} used to suggest a lower-bounded wildcard,
     * but no wildcard is involved: when the functional interface method parameter is one,
     * {@code LambdaExprContext} already stores its bounded type here.
     */
    @Override
    public String describe() {
        return bound.describe();
    }

    public ResolvedType getBound() {
        return bound;
    }

    @Override
    public boolean isConstraint() {
        return true;
    }

    @Override
    public ResolvedLambdaConstraintType asConstraintType() {
        return this;
    }

    public static ResolvedLambdaConstraintType bound(ResolvedType bound) {
        return new ResolvedLambdaConstraintType(bound);
    }

    @Override
    public boolean isAssignableBy(ResolvedType other) {
        return bound.isAssignableBy(other);
    }

    @Override
    public String toString() {
        return "LambdaConstraintType{" + "bound=" + bound + '}';
    }
}
