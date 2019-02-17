package com.github.javaparser.symbolsolver.javaparsermodel.declarations;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.nodeTypes.NodeWithMembers;
import com.github.javaparser.ast.nodeTypes.NodeWithSimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.resolution.declarations.ResolvedFieldDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.resolution.SymbolSolver;

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
                String prefix = internalType.getName() + ".";
                if (internalType.getName().getId().equals(name)) {
                    if (internalType instanceof ClassOrInterfaceDeclaration) {
                        if (((ClassOrInterfaceDeclaration) internalType).isInterface()) {
                            return SymbolReference.solved(new JavaParserInterfaceDeclaration((com.github.javaparser.ast.body.ClassOrInterfaceDeclaration) internalType, typeSolver));
                        } else {
                            return SymbolReference.solved(new JavaParserClassDeclaration((com.github.javaparser.ast.body.ClassOrInterfaceDeclaration) internalType, typeSolver));
                        }
                    } else if (internalType instanceof EnumDeclaration) {
                        return SymbolReference.solved(new JavaParserEnumDeclaration((com.github.javaparser.ast.body.EnumDeclaration) internalType, typeSolver));
                    } else {
                        throw new UnsupportedOperationException();
                    }
                } else if (name.startsWith(prefix) && name.length() > prefix.length()) {
                    if (internalType instanceof ClassOrInterfaceDeclaration) {
                        if (((ClassOrInterfaceDeclaration) internalType).isInterface()) {
                            return new JavaParserInterfaceDeclaration((com.github.javaparser.ast.body.ClassOrInterfaceDeclaration) internalType, typeSolver).solveType(name.substring(prefix.length()));
                        } else {
                            return new JavaParserClassDeclaration((com.github.javaparser.ast.body.ClassOrInterfaceDeclaration) internalType, typeSolver).solveType(name.substring(prefix.length()));
                        }
                    } else if (internalType instanceof EnumDeclaration) {
                        return new SymbolSolver(typeSolver).solveTypeInType(new JavaParserEnumDeclaration((com.github.javaparser.ast.body.EnumDeclaration) internalType, typeSolver), name.substring(prefix.length()));
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
}
