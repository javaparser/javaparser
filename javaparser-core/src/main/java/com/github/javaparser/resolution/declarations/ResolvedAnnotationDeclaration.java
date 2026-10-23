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
package com.github.javaparser.resolution.declarations;

import com.github.javaparser.resolution.types.ResolvedType;
import java.lang.annotation.Annotation;
import java.util.List;

/**
 * @author Federico Tomassetti
 */
public interface ResolvedAnnotationDeclaration extends ResolvedReferenceTypeDeclaration {

    @Override
    default boolean isAnnotation() {
        return true;
    }

    @Override
    default ResolvedAnnotationDeclaration asAnnotation() {
        return this;
    }

    List<ResolvedAnnotationMemberDeclaration> getAnnotationMembers();

    boolean isInheritable();

    @Override
    default boolean isAssignableBy(ResolvedType type) {
        if (type.isNull()) {
            return true;
        }
        if (type.isReferenceType()) {
            return type.asReferenceType()
                    .getTypeDeclaration()
                    .map(this::isAssignableBy)
                    .orElse(false);
        }
        return false;
    }

    @Override
    default boolean isAssignableBy(ResolvedReferenceTypeDeclaration other) {
        // Delegating to other.canBeAssignedTo(this) would recurse infinitely
        if (other.getQualifiedName().equals(getQualifiedName())) {
            return true;
        }
        return other.getAllAncestors().stream()
                .anyMatch(ancestor -> ancestor.getQualifiedName().equals(getQualifiedName()));
    }

    /**
     * The supertypes of an annotation interface are {@link Annotation} and {@link Object} (JLS 4.10.2, 9.6).
     */
    @Override
    default boolean canBeAssignedTo(ResolvedReferenceTypeDeclaration other) {
        return other.isJavaLangObject()
                || other.getQualifiedName().equals(getQualifiedName())
                || other.getQualifiedName().equals(Annotation.class.getCanonicalName());
    }
}
