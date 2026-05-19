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

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.nodeTypes.NodeWithMembers;
import com.github.javaparser.ast.nodeTypes.NodeWithSimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.SymbolSolver;
import java.util.*;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
public class JavaParserTypeAdapter<
        T extends Node & NodeWithSimpleName<T> & NodeWithMembers<T> & NodeWithAnnotations<T>> {

    private T wrappedNode;
    private TypeSolver typeSolver;

    public JavaParserTypeAdapter(T wrappedNode, TypeSolver typeSolver) {
        this.wrappedNode = wrappedNode;
        this.typeSolver = typeSolver;
    }

    public String getPackageName() {
        return AstResolutionUtils.getPackageName(wrappedNode);
    }

    public String getClassName() {
        return AstResolutionUtils.getClassName("", wrappedNode);
    }

    public String getQualifiedName() {
        String containerName =
                AstResolutionUtils.containerName(wrappedNode.getParentNode().orElse(null));
        if (containerName.isEmpty()) {
            return wrappedNode.getName().getId();
        }
        return containerName + "." + wrappedNode.getName().getId();
    }

    public boolean isAssignableBy(ResolvedReferenceTypeDeclaration other) {
        List<ResolvedReferenceType> ancestorsOfOther = other.getAllAncestors();
        ancestorsOfOther.add(new ReferenceTypeImpl(other));
        for (ResolvedReferenceType ancestorOfOther : ancestorsOfOther) {
            if (ancestorOfOther.getQualifiedName().equals(this.getQualifiedName())) {
                return true;
            }
        }
        return false;
    }

    public boolean isAssignableBy(ResolvedType type) {
        if (type.isNull()) {
            return true;
        }
        if (type.isReferenceType()) {
            ResolvedReferenceTypeDeclaration other = typeSolver.solveType(type.describe());
            return isAssignableBy(other);
        }
        throw new UnsupportedOperationException();
    }

    /**
     * Resolution should move out of declarations, so that they are pure declarations and the resolution should
     * work for JavaParser, Reflection and Javassist classes in the same way and not be specific to the three
     * implementations.
     */
    @Deprecated
    public SymbolReference<ResolvedTypeDeclaration> solveType(String name) {
        if (wrappedNode instanceof NodeWithTypeParameters<?> parameters) {
            NodeList<TypeParameter> typeParameters = parameters.getTypeParameters();
            for (com.github.javaparser.ast.type.TypeParameter typeParameter : typeParameters) {
                if (typeParameter.getName().getId().equals(name)) {
                    return SymbolReference.solved(new JavaParserTypeVariableDeclaration(typeParameter, typeSolver));
                }
            }
        }

        // Member classes & interfaces
        for (BodyDeclaration<?> member : this.wrappedNode.getMembers()) {
            if (member instanceof com.github.javaparser.ast.body.TypeDeclaration<?> internalType) {
                String prefix = internalType.getName().asString() + ".";
                if (internalType.getName().getId().equals(name)) {
                    if (internalType instanceof ClassOrInterfaceDeclaration declaration) {
                        if (declaration.isInterface()) {
                            return SymbolReference.solved(new JavaParserInterfaceDeclaration(
                                    declaration,
                                    typeSolver));
                        }
                        return SymbolReference.solved(new JavaParserClassDeclaration(
                                declaration, typeSolver));
                    }
                    if (internalType instanceof com.github.javaparser.ast.body.EnumDeclaration declaration1) {
                        return SymbolReference.solved(new JavaParserEnumDeclaration(
                                declaration1, typeSolver));
                    }
                    if (internalType instanceof com.github.javaparser.ast.body.AnnotationDeclaration declaration2) {
                        return SymbolReference.solved(new JavaParserAnnotationDeclaration(
                                declaration2, typeSolver));
                    }
                    if (internalType instanceof com.github.javaparser.ast.body.RecordDeclaration declaration3) {
                        return SymbolReference.solved(new JavaParserRecordDeclaration(
                                declaration3, typeSolver));
                    }
                    throw new UnsupportedOperationException();
                }
                if (name.startsWith(prefix) && name.length() > prefix.length()) {
                    if (internalType instanceof ClassOrInterfaceDeclaration declaration4) {
                        if (declaration4.isInterface()) {
                            return new JavaParserInterfaceDeclaration(
                                            declaration4,
                                            typeSolver)
                                    .solveType(name.substring(prefix.length()));
                        }
                        return new JavaParserClassDeclaration(
                                        declaration4,
                                        typeSolver)
                                .solveType(name.substring(prefix.length()));
                    }
                    if (internalType instanceof com.github.javaparser.ast.body.EnumDeclaration declaration5) {
                        return new SymbolSolver(typeSolver)
                                .solveTypeInType(
                                        new JavaParserEnumDeclaration(
                                                declaration5,
                                                typeSolver),
                                        name.substring(prefix.length()));
                    }
                    if (internalType instanceof com.github.javaparser.ast.body.AnnotationDeclaration declaration6) {
                        return SymbolReference.solved(new JavaParserAnnotationDeclaration(
                                declaration6, typeSolver));
                    }
                    throw new UnsupportedOperationException();
                }
            }
        }
        return SymbolReference.unsolved();
    }

    public Optional<ResolvedReferenceTypeDeclaration> containerType() {
        return wrappedNode
                .getParentNode()
                .filter(parentNode -> !(parentNode instanceof CompilationUnit))
                .map(node -> node.getSymbolResolver().toTypeDeclaration(node));
    }

    public List<ResolvedFieldDeclaration> getFieldsForDeclaredVariables() {
        List<ResolvedFieldDeclaration> fields = new ArrayList<>();
        if (wrappedNode.getMembers() != null) {
            for (BodyDeclaration<?> member : this.wrappedNode.getMembers()) {
                if (member.isFieldDeclaration()) {
                    FieldDeclaration field = member.asFieldDeclaration();
                    for (VariableDeclarator vd : field.getVariables()) {
                        fields.add(new JavaParserFieldDeclaration(vd, typeSolver));
                    }
                }
            }
        }
        return fields;
    }

    /*
     * Returns a set of the declared annotation on this type
     */
    public Set<ResolvedAnnotationDeclaration> getDeclaredAnnotations() {
        return wrappedNode.getAnnotations().stream()
                .map(annotation -> annotation.resolve())
                .collect(Collectors.toSet());
    }

    /*
     * Returns a set of the declared methods on this type
     */
    public Set<ResolvedMethodDeclaration> getDeclaredMethods() {
        Set<ResolvedMethodDeclaration> methods = new HashSet<>();
        for (BodyDeclaration<?> member : wrappedNode.getMembers()) {
            if (member instanceof MethodDeclaration declaration) {
                methods.add(new JavaParserMethodDeclaration(declaration, typeSolver));
            }
        }
        return methods;
    }

    public Set<ResolvedReferenceTypeDeclaration> internalTypes() {
        // Use a special Set implementation that avoids calculating the hashCode of the node,
        // since this can be very time-consuming for big node trees, and we are sure there are
        // no duplicates in the members list.
        Set<ResolvedReferenceTypeDeclaration> res = Collections.newSetFromMap(new IdentityHashMap<>());
        for (BodyDeclaration<?> member : this.wrappedNode.getMembers()) {
            if (member instanceof TypeDeclaration declaration) {
                res.add(JavaParserFacade.get(typeSolver).getTypeDeclaration(declaration));
            }
        }
        return res;
    }
}
