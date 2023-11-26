/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2023 The JavaParser Team.
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

import java.util.*;
import java.util.stream.Collectors;

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.resolution.Context;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.core.resolution.MethodUsageResolutionCapability;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.ObjectCreationContext;
import com.github.javaparser.symbolsolver.logic.AbstractClassDeclaration;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;

/**
 * An anonymous class declaration representation.
 */
public class JavaParserAnonymousClassDeclaration extends AbstractClassDeclaration
        implements MethodUsageResolutionCapability {

    private final TypeSolver typeSolver;
    private final ObjectCreationExpr wrappedNode;
    private final ResolvedTypeDeclaration superTypeDeclaration;
    private final String name = "Anonymous-" + UUID.randomUUID();

    public JavaParserAnonymousClassDeclaration(ObjectCreationExpr wrappedNode,
                                               TypeSolver typeSolver) {
        this.typeSolver = typeSolver;
        this.wrappedNode = wrappedNode;

        ClassOrInterfaceType superType = wrappedNode.getType();
        String superTypeName = superType.getName().getId();
        if (superType.getScope().isPresent()) {
            superTypeName = superType.getScope().get().asString() + "." + superTypeName;
        }

        Context context = new ObjectCreationContext(wrappedNode, typeSolver);
        superTypeDeclaration = context.solveType(superTypeName).getCorrespondingDeclaration();
    }

    public ResolvedTypeDeclaration getSuperTypeDeclaration() {
        return superTypeDeclaration;
    }

    public <T extends Node> List<T> findMembersOfKind(final Class<T> memberClass) {
        if (wrappedNode.getAnonymousClassBody().isPresent()) {
            return wrappedNode
                    .getAnonymousClassBody()
                    .get()
                    .stream()
                    .filter(node -> memberClass.isAssignableFrom(node.getClass()))
                    .map(memberClass::cast)
                    .collect(Collectors.toList());
        }
        return Collections.emptyList();
    }

    public Context getContext() {
        return JavaParserFactory.getContext(wrappedNode, typeSolver);
    }

    @Override
    public SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> argumentsTypes,
                                                                  boolean staticOnly) {
        return getContext().solveMethod(name, argumentsTypes, staticOnly);
    }

    @Override
    public Optional<MethodUsage> solveMethodAsUsage(String name, List<ResolvedType> argumentTypes,
                                                    Context invocationContext, List<ResolvedType> typeParameters) {
        return getContext().solveMethodAsUsage(name, argumentTypes);
    }

    @Override
    protected ResolvedReferenceType object() {
        return new ReferenceTypeImpl(typeSolver.getSolvedJavaLangObject());
    }

    @Override
    public Optional<ResolvedReferenceType> getSuperClass() {
        ResolvedReferenceTypeDeclaration superRRTD = superTypeDeclaration.asReferenceType();
        if (superRRTD == null) {
            return Optional.empty();
        }
        return Optional.of(new ReferenceTypeImpl(superRRTD));
    }

    @Override
    public List<ResolvedReferenceType> getInterfaces() {
        return superTypeDeclaration.asReferenceType()
                .getAncestors()
                .stream()
                .filter(type -> type.getTypeDeclaration().isPresent())
                .filter(type -> type.getTypeDeclaration().get().isInterface())
                .collect(Collectors.toList());
    }

    @Override
    public List<ResolvedConstructorDeclaration> getConstructors() {
        if (superTypeDeclaration.isInterface()) {
            return Collections.singletonList(new DefaultConstructorDeclaration<>(this));
        }
        return superTypeDeclaration.asReferenceType().getConstructors();
    }

    @Override
    public AccessSpecifier accessSpecifier() {
        return AccessSpecifier.PRIVATE;
    }

    @Override
    public List<ResolvedReferenceType> getAncestors(boolean acceptIncompleteList) {
        ImmutableList.Builder<ResolvedReferenceType> builder = ImmutableList.builder();

        // Only add the super type if it is present (e.g. java.lang.Object has no super class)
        getSuperClass().ifPresent(builder::add);

        // All all ancestors of the super type..?
        builder.addAll(superTypeDeclaration.asReferenceType().getAncestors(acceptIncompleteList));

        return builder.build();
    }

    @Override
    public List<ResolvedFieldDeclaration> getAllFields() {

        List<JavaParserFieldDeclaration> myFields = findMembersOfKind(FieldDeclaration.class)
                .stream()
                .flatMap(field -> field.getVariables()
                        .stream()
                        .map(variable -> new JavaParserFieldDeclaration(variable, typeSolver))
                )
                .collect(Collectors.toList());


        // TODO: Figure out if it is appropriate to remove the orElseThrow() -- if so, how...
        List<ResolvedFieldDeclaration> superClassFields = getSuperClass()
                .orElseThrow(() -> new RuntimeException("super class unexpectedly empty"))
                .getTypeDeclaration()
                .orElseThrow(() -> new RuntimeException("TypeDeclaration unexpectedly empty."))
                .getAllFields();

        // TODO: Figure out if it is appropriate to remove the orElseThrow() -- if so, how...
        List<ResolvedFieldDeclaration> interfaceFields =
                getInterfaces().stream()
                        .flatMap(interfaceReferenceType -> interfaceReferenceType
                                .getTypeDeclaration().orElseThrow(() -> new RuntimeException("TypeDeclaration unexpectedly empty."))
                                .getAllFields()
                                .stream()
                        )
                        .collect(Collectors.toList());

        return ImmutableList
                .<ResolvedFieldDeclaration>builder()
                .addAll(myFields)
                .addAll(superClassFields)
                .addAll(interfaceFields)
                .build();
    }

    @Override
    public Set<ResolvedMethodDeclaration> getDeclaredMethods() {
        return
                findMembersOfKind(MethodDeclaration.class)
                        .stream()
                        .map(method -> new JavaParserMethodDeclaration(method, typeSolver))
                        .collect(Collectors.toSet());
    }

    @Override
    public boolean isAssignableBy(ResolvedType type) {
        return false;
    }

    @Override
    public boolean isAssignableBy(ResolvedReferenceTypeDeclaration other) {
        return false;
    }

    @Override
    public boolean hasDirectlyAnnotation(String qualifiedName) {
        return false;
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
            return getName();
        }
        return containerName + "." + getName();
    }

    @Override
    public Set<ResolvedReferenceTypeDeclaration> internalTypes() {
        return
                findMembersOfKind(TypeDeclaration.class)
                        .stream()
                        .map(typeMember -> JavaParserFacade.get(typeSolver).getTypeDeclaration(typeMember))
                        .collect(Collectors.toSet());
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public List<ResolvedTypeParameterDeclaration> getTypeParameters() {
        return Lists.newArrayList();
    }

    @Override
    public Optional<ResolvedReferenceTypeDeclaration> containerType() {
        throw new UnsupportedOperationException("containerType is not supported for " + this.getClass().getCanonicalName());
    }

    @Override
    public Optional<Node> toAst() {
        return Optional.of(wrappedNode);
    }

}
