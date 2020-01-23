/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2020 The JavaParser Team.
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

package org.javaparser.symbolsolver.javaparsermodel.declarations;

import org.javaparser.ast.body.AnnotationDeclaration;
import org.javaparser.ast.body.AnnotationMemberDeclaration;
import org.javaparser.resolution.declarations.*;
import org.javaparser.resolution.types.ResolvedReferenceType;
import org.javaparser.resolution.types.ResolvedType;
import org.javaparser.symbolsolver.logic.AbstractTypeDeclaration;
import org.javaparser.symbolsolver.model.resolution.TypeSolver;

import java.util.Collections;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
public class JavaParserAnnotationDeclaration extends AbstractTypeDeclaration implements ResolvedAnnotationDeclaration {

    private org.javaparser.ast.body.AnnotationDeclaration wrappedNode;
    private TypeSolver typeSolver;

    public JavaParserAnnotationDeclaration(AnnotationDeclaration wrappedNode, TypeSolver typeSolver) {
        this.wrappedNode = wrappedNode;
        this.typeSolver = typeSolver;
    }

    @Override
    public List<ResolvedReferenceType> getAncestors(boolean acceptIncompleteList) {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<ResolvedFieldDeclaration> getAllFields() {
        // TODO #1837
        throw new UnsupportedOperationException();
    }

    @Override
    public Set<ResolvedMethodDeclaration> getDeclaredMethods() {
        // TODO #1838
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isAssignableBy(ResolvedType type) {
        // TODO #1836
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isAssignableBy(ResolvedReferenceTypeDeclaration other) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean hasDirectlyAnnotation(String canonicalName) {
        return AstResolutionUtils.hasDirectlyAnnotation(wrappedNode, typeSolver, canonicalName);
    }

    @Override
    public String getPackageName() {
        return AstResolutionUtils.getPackageName(wrappedNode);
    }

    @Override
    public String getClassName() {
        return AstResolutionUtils.getClassName("", wrappedNode);
    }

    @Override
    public String getQualifiedName() {
        String containerName = AstResolutionUtils.containerName(wrappedNode.getParentNode().orElse(null));
        if (containerName.isEmpty()) {
            return wrappedNode.getName().getId();
        } else {
            return containerName + "." + wrappedNode.getName();
        }
    }

    @Override
    public String getName() {
        return wrappedNode.getName().getId();
    }

    /**
     * Annotation declarations cannot have type parameters and hence this method always returns an empty list.
     *
     * @return An empty list.
     */
    @Override
    public List<ResolvedTypeParameterDeclaration> getTypeParameters() {
        // Annotation declarations cannot have type parameters - i.e. we can always return an empty list.
        return Collections.emptyList();
    }

    @Override
    public Optional<ResolvedReferenceTypeDeclaration> containerType() {
        // TODO #1841
        throw new UnsupportedOperationException("containerType is not supported for " + this.getClass().getCanonicalName());
    }

    @Override
    public List<ResolvedAnnotationMemberDeclaration> getAnnotationMembers() {
        return wrappedNode.getMembers().stream()
                .filter(m -> m instanceof AnnotationMemberDeclaration)
                .map(m -> new JavaParserAnnotationMemberDeclaration((AnnotationMemberDeclaration)m, typeSolver))
                .collect(Collectors.toList());
    }

    @Override
    public List<ResolvedConstructorDeclaration> getConstructors() {
        return Collections.emptyList();
    }

    @Override
    public Optional<AnnotationDeclaration> toAst() {
        return Optional.of(wrappedNode);
    }
}
