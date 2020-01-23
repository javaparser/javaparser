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

import org.javaparser.ast.Node;
import org.javaparser.ast.NodeList;
import org.javaparser.ast.body.BodyDeclaration;
import org.javaparser.ast.body.ClassOrInterfaceDeclaration;
import org.javaparser.ast.body.EnumDeclaration;
import org.javaparser.ast.body.VariableDeclarator;
import org.javaparser.ast.nodeTypes.NodeWithMembers;
import org.javaparser.ast.nodeTypes.NodeWithSimpleName;
import org.javaparser.ast.nodeTypes.NodeWithTypeParameters;
import org.javaparser.ast.type.TypeParameter;
import org.javaparser.resolution.declarations.ResolvedFieldDeclaration;
import org.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import org.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import org.javaparser.resolution.types.ResolvedReferenceType;
import org.javaparser.resolution.types.ResolvedType;
import org.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import org.javaparser.symbolsolver.model.resolution.SymbolReference;
import org.javaparser.symbolsolver.model.resolution.TypeSolver;
import org.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import org.javaparser.symbolsolver.resolution.SymbolSolver;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * @author Federico Tomassetti
 */
public class JavaParserTypeAdapter<T extends Node & NodeWithSimpleName<T> & NodeWithMembers<T>> {

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
        } else {
            return containerName + "." + wrappedNode.getName().getId();
        }
    }

    public boolean isAssignableBy(ResolvedReferenceTypeDeclaration other) {
        List<ResolvedReferenceType> ancestorsOfOther = other.getAllAncestors();
        ancestorsOfOther.add(new ReferenceTypeImpl(other, typeSolver));
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
        } else {
            throw new UnsupportedOperationException();
        }
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
            for (org.javaparser.ast.type.TypeParameter typeParameter : typeParameters) {
                if (typeParameter.getName().getId().equals(name)) {
                    return SymbolReference.solved(new JavaParserTypeVariableDeclaration(typeParameter, typeSolver));
                }
            }
        }

        // Member classes & interfaces
        for (BodyDeclaration<?> member : this.wrappedNode.getMembers()) {
            if (member instanceof org.javaparser.ast.body.TypeDeclaration) {
                org.javaparser.ast.body.TypeDeclaration<?> internalType = (org.javaparser.ast.body.TypeDeclaration<?>) member;
                String prefix = internalType.getName() + ".";
                if (internalType.getName().getId().equals(name)) {
                    if (internalType instanceof ClassOrInterfaceDeclaration) {
                        if (((ClassOrInterfaceDeclaration) internalType).isInterface()) {
                            return SymbolReference.solved(new JavaParserInterfaceDeclaration((org.javaparser.ast.body.ClassOrInterfaceDeclaration) internalType, typeSolver));
                        } else {
                            return SymbolReference.solved(new JavaParserClassDeclaration((org.javaparser.ast.body.ClassOrInterfaceDeclaration) internalType, typeSolver));
                        }
                    } else if (internalType instanceof EnumDeclaration) {
                        return SymbolReference.solved(new JavaParserEnumDeclaration((org.javaparser.ast.body.EnumDeclaration) internalType, typeSolver));
                    } else {
                        throw new UnsupportedOperationException();
                    }
                } else if (name.startsWith(prefix) && name.length() > prefix.length()) {
                    if (internalType instanceof ClassOrInterfaceDeclaration) {
                        if (((ClassOrInterfaceDeclaration) internalType).isInterface()) {
                            return new JavaParserInterfaceDeclaration((org.javaparser.ast.body.ClassOrInterfaceDeclaration) internalType, typeSolver).solveType(name.substring(prefix.length()));
                        } else {
                            return new JavaParserClassDeclaration((org.javaparser.ast.body.ClassOrInterfaceDeclaration) internalType, typeSolver).solveType(name.substring(prefix.length()));
                        }
                    } else if (internalType instanceof EnumDeclaration) {
                        return new SymbolSolver(typeSolver).solveTypeInType(new JavaParserEnumDeclaration((org.javaparser.ast.body.EnumDeclaration) internalType, typeSolver), name.substring(prefix.length()));
                    } else {
                        throw new UnsupportedOperationException();
                    }
                }
            }
        }
        return SymbolReference.unsolved(ResolvedTypeDeclaration.class);
    }

    public Optional<ResolvedReferenceTypeDeclaration> containerType() {
        return wrappedNode
                .getParentNode()
                .map(node -> JavaParserFactory.toTypeDeclaration(node, typeSolver));
    }
    
    public List<ResolvedFieldDeclaration> getFieldsForDeclaredVariables() {
        List<ResolvedFieldDeclaration> fields = new ArrayList<>();
        if (wrappedNode.getMembers() != null) {
            for (BodyDeclaration<?> member : this.wrappedNode.getMembers()) {
                if (member instanceof org.javaparser.ast.body.FieldDeclaration) {
                    org.javaparser.ast.body.FieldDeclaration field = (org.javaparser.ast.body.FieldDeclaration) member;
                    for (VariableDeclarator vd : field.getVariables()) {
                        fields.add(new JavaParserFieldDeclaration(vd, typeSolver));
                    }
                }
            }
        }
        return fields;
    }
}
