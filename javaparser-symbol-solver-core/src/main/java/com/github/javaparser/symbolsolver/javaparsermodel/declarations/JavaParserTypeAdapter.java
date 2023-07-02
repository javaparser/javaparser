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

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.nodeTypes.NodeWithMembers;
import com.github.javaparser.ast.nodeTypes.NodeWithSimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedAnnotationDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedFieldDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.SymbolSolver;

/**
 * @author Federico Tomassetti
 */
public class JavaParserTypeAdapter<T extends Node & NodeWithSimpleName<T> & NodeWithMembers<T> & NodeWithAnnotations<T>> {

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
        String containerName = AstResolutionUtils.containerName(wrappedNode.getParentNode().orElse(null));
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
     * This method is deprecated because it receives the TypesSolver as a parameter.
     * Eventually we would like to remove all usages of TypeSolver as a parameter.
     *
     * Also, resolution should move out of declarations, so that they are pure declarations and the resolution should
     * work for JavaParser, Reflection and Javassist classes in the same way and not be specific to the three
     * implementations.
     */
    @Deprecated
    public SymbolReference<ResolvedTypeDeclaration> solveType(String name) {
        if(wrappedNode instanceof NodeWithTypeParameters<?>) {
            NodeList<TypeParameter> typeParameters = ((NodeWithTypeParameters<?>) wrappedNode).getTypeParameters();
            for (com.github.javaparser.ast.type.TypeParameter typeParameter : typeParameters) {
                if (typeParameter.getName().getId().equals(name)) {
                    return SymbolReference.solved(new JavaParserTypeVariableDeclaration(typeParameter, typeSolver));
                }
            }
        }

        // Member classes & interfaces
        for (BodyDeclaration<?> member : this.wrappedNode.getMembers()) {
            if (member instanceof com.github.javaparser.ast.body.TypeDeclaration) {
                com.github.javaparser.ast.body.TypeDeclaration<?> internalType = (com.github.javaparser.ast.body.TypeDeclaration<?>) member;
                String prefix = internalType.getName().asString() + ".";
                if (internalType.getName().getId().equals(name)) {
                    if (internalType instanceof ClassOrInterfaceDeclaration) {
                        if (((ClassOrInterfaceDeclaration) internalType).isInterface()) {
                            return SymbolReference.solved(new JavaParserInterfaceDeclaration((com.github.javaparser.ast.body.ClassOrInterfaceDeclaration) internalType, typeSolver));
                        }
                        return SymbolReference.solved(new JavaParserClassDeclaration((com.github.javaparser.ast.body.ClassOrInterfaceDeclaration) internalType, typeSolver));
                    }
                                    if (internalType instanceof EnumDeclaration) {
                        return SymbolReference.solved(new JavaParserEnumDeclaration((com.github.javaparser.ast.body.EnumDeclaration) internalType, typeSolver));
                    }
                                    if (internalType instanceof AnnotationDeclaration) {
                        return SymbolReference.solved(new JavaParserAnnotationDeclaration((com.github.javaparser.ast.body.AnnotationDeclaration) internalType, typeSolver));
                    }
                    throw new UnsupportedOperationException();
                }
                if (name.startsWith(prefix) && name.length() > prefix.length()) {
                    if (internalType instanceof ClassOrInterfaceDeclaration) {
                        if (((ClassOrInterfaceDeclaration) internalType).isInterface()) {
                            return new JavaParserInterfaceDeclaration((com.github.javaparser.ast.body.ClassOrInterfaceDeclaration) internalType, typeSolver).solveType(name.substring(prefix.length()));
                        }
                        return new JavaParserClassDeclaration((com.github.javaparser.ast.body.ClassOrInterfaceDeclaration) internalType, typeSolver).solveType(name.substring(prefix.length()));
                    }
                                    if (internalType instanceof EnumDeclaration) {
                        return new SymbolSolver(typeSolver).solveTypeInType(new JavaParserEnumDeclaration((com.github.javaparser.ast.body.EnumDeclaration) internalType, typeSolver), name.substring(prefix.length()));
                    }
                                    if (internalType instanceof AnnotationDeclaration) {
                        return SymbolReference.solved(new JavaParserAnnotationDeclaration((com.github.javaparser.ast.body.AnnotationDeclaration) internalType, typeSolver));
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
                .map(node -> node.getSymbolResolver().toTypeDeclaration(node));
    }

    public List<ResolvedFieldDeclaration> getFieldsForDeclaredVariables() {
        List<ResolvedFieldDeclaration> fields = new ArrayList<>();
        if (wrappedNode.getMembers() != null) {
            for (BodyDeclaration<?> member : this.wrappedNode.getMembers()) {
                if (member instanceof com.github.javaparser.ast.body.FieldDeclaration) {
                    com.github.javaparser.ast.body.FieldDeclaration field = (com.github.javaparser.ast.body.FieldDeclaration) member;
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

    public Set<ResolvedReferenceTypeDeclaration> internalTypes() {
        // Use a special Set implementation that avoids calculating the hashCode of the node,
        // since this can be very time-consuming for big node trees, and we are sure there are
        // no duplicates in the members list.
        Set<ResolvedReferenceTypeDeclaration> res = Collections.newSetFromMap(new IdentityHashMap<>());
        for (BodyDeclaration<?> member : this.wrappedNode.getMembers()) {
            if (member instanceof TypeDeclaration) {
                res.add(JavaParserFacade.get(typeSolver).getTypeDeclaration((TypeDeclaration) member));
            }
        }
        return res;
    }
}
