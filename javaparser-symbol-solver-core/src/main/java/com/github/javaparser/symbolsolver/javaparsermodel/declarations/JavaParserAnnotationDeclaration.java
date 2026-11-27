/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2026 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.javaparsermodel.declarations;

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.AnnotationDeclaration;
import com.github.javaparser.ast.body.AnnotationMemberDeclaration;
import com.github.javaparser.resolution.Context;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.logic.MethodResolutionCapability;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.core.resolution.MethodUsageResolutionCapability;
import com.github.javaparser.symbolsolver.core.resolution.TypeVariableResolutionCapability;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.logic.AbstractTypeDeclaration;
import com.github.javaparser.symbolsolver.logic.MemberResolutionLogic;
import java.lang.annotation.Inherited;
import java.util.*;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
public class JavaParserAnnotationDeclaration extends AbstractTypeDeclaration
        implements ResolvedAnnotationDeclaration, MethodResolutionCapability, MethodUsageResolutionCapability {

    private com.github.javaparser.ast.body.AnnotationDeclaration wrappedNode;
    private TypeSolver typeSolver;
    private JavaParserTypeAdapter<AnnotationDeclaration> javaParserTypeAdapter;

    public JavaParserAnnotationDeclaration(AnnotationDeclaration wrappedNode, TypeSolver typeSolver) {
        this.wrappedNode = wrappedNode;
        this.typeSolver = typeSolver;
        this.javaParserTypeAdapter = new JavaParserTypeAdapter<>(wrappedNode, typeSolver);
    }

    @Override
    public List<ResolvedReferenceType> getAncestors(boolean acceptIncompleteList) {
        List<ResolvedReferenceType> ancestors = new ArrayList<>();
        ancestors.add(new ReferenceTypeImpl(typeSolver.solveType("java.lang.annotation.Annotation")));
        return ancestors;
    }

    @Override
    public Set<ResolvedReferenceTypeDeclaration> internalTypes() {
        return javaParserTypeAdapter.internalTypes();
    }

    @Override
    public List<ResolvedFieldDeclaration> getAllFields() {
        return wrappedNode.getFields().stream()
                .flatMap(field -> field.getVariables().stream())
                .map(var -> new JavaParserFieldDeclaration(var, typeSolver))
                .collect(Collectors.toList());
    }

    @Override
    public Set<ResolvedMethodDeclaration> getDeclaredMethods() {
        return wrappedNode.getMembers().stream()
                .filter(m -> m instanceof AnnotationMemberDeclaration)
                .map(m -> new AnnotationMemberMethodDeclaration((AnnotationMemberDeclaration) m, this, typeSolver))
                .collect(Collectors.toSet());
    }

    public Context getContext() {
        return JavaParserFactory.getContext(wrappedNode, typeSolver);
    }

    @Override
    public SymbolReference<ResolvedMethodDeclaration> solveMethod(
            String name, List<ResolvedType> argumentsTypes, boolean staticOnly) {
        return MemberResolutionLogic.solveMethodInMembers(this, name, argumentsTypes, staticOnly, typeSolver);
    }

    @Override
    public Optional<MethodUsage> solveMethodAsUsage(
            String name,
            List<ResolvedType> argumentTypes,
            Context invocationContext,
            List<ResolvedType> typeParameters) {
        return MemberResolutionLogic.solveMethodAsUsageInMembers(
                this, name, argumentTypes, getContext(), typeParameters, typeSolver);
    }

    @Override
    public boolean hasDirectlyAnnotation(String canonicalName) {
        return AstResolutionUtils.hasDirectlyAnnotation(wrappedNode, typeSolver, canonicalName);
    }

    /*
     * Returns a set of the declared annotation on this type
     */
    @Override
    public Set<ResolvedAnnotationDeclaration> getDeclaredAnnotations() {
        return javaParserTypeAdapter.getDeclaredAnnotations();
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
        String containerName =
                AstResolutionUtils.containerName(wrappedNode.getParentNode().orElse(null));
        if (containerName.isEmpty()) {
            return wrappedNode.getName().getId();
        }
        return containerName + "." + wrappedNode.getName();
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
        throw new UnsupportedOperationException(
                "containerType is not supported for " + this.getClass().getCanonicalName());
    }

    @Override
    public List<ResolvedAnnotationMemberDeclaration> getAnnotationMembers() {
        return wrappedNode.getMembers().stream()
                .filter(m -> m instanceof AnnotationMemberDeclaration)
                .map(m -> new JavaParserAnnotationMemberDeclaration((AnnotationMemberDeclaration) m, typeSolver))
                .collect(Collectors.toList());
    }

    @Override
    public List<ResolvedConstructorDeclaration> getConstructors() {
        return Collections.emptyList();
    }

    @Override
    public boolean isInheritable() {
        return wrappedNode.getAnnotationByClass(Inherited.class).isPresent();
    }

    @Override
    public Optional<Node> toAst() {
        return Optional.of(wrappedNode);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        JavaParserAnnotationDeclaration that = (JavaParserAnnotationDeclaration) o;
        return wrappedNode.equals(that.wrappedNode);
    }

    @Override
    public int hashCode() {
        return wrappedNode.hashCode();
    }

    private static class AnnotationMemberMethodDeclaration
            implements ResolvedMethodDeclaration, TypeVariableResolutionCapability {

        private final AnnotationMemberDeclaration wrappedNode;
        private final JavaParserAnnotationDeclaration declaringType;
        private final TypeSolver typeSolver;

        private AnnotationMemberMethodDeclaration(
                AnnotationMemberDeclaration wrappedNode,
                JavaParserAnnotationDeclaration declaringType,
                TypeSolver typeSolver) {
            this.wrappedNode = wrappedNode;
            this.declaringType = declaringType;
            this.typeSolver = typeSolver;
        }

        @Override
        public AccessSpecifier accessSpecifier() {
            return AccessSpecifier.PUBLIC;
        }

        @Override
        public String getName() {
            return wrappedNode.getNameAsString();
        }

        @Override
        public ResolvedType getReturnType() {
            return JavaParserFacade.get(typeSolver)
                    .convert(wrappedNode.getType(), JavaParserFactory.getContext(wrappedNode, typeSolver));
        }

        @Override
        public boolean isAbstract() {
            return true;
        }

        @Override
        public boolean isDefaultMethod() {
            return false;
        }

        @Override
        public boolean isStatic() {
            return false;
        }

        @Override
        public String toDescriptor() {
            return String.format("()%s", getReturnType().toDescriptor());
        }

        @Override
        public ResolvedReferenceTypeDeclaration declaringType() {
            return declaringType;
        }

        @Override
        public int getNumberOfParams() {
            return 0;
        }

        @Override
        public ResolvedParameterDeclaration getParam(int i) {
            throw new IllegalArgumentException("Annotation members do not have parameters");
        }

        @Override
        public int getNumberOfSpecifiedExceptions() {
            return 0;
        }

        @Override
        public ResolvedType getSpecifiedException(int index) {
            throw new IllegalArgumentException("Annotation members do not throw exceptions");
        }

        @Override
        public List<ResolvedTypeParameterDeclaration> getTypeParameters() {
            return Collections.emptyList();
        }

        @Override
        public MethodUsage resolveTypeVariables(Context context, List<ResolvedType> parameterTypes) {
            return new MethodUsage(this);
        }

        @Override
        public Optional<Node> toAst() {
            return Optional.of(wrappedNode);
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            AnnotationMemberMethodDeclaration that = (AnnotationMemberMethodDeclaration) o;
            return wrappedNode.equals(that.wrappedNode);
        }

        @Override
        public int hashCode() {
            return wrappedNode.hashCode();
        }
    }
}
