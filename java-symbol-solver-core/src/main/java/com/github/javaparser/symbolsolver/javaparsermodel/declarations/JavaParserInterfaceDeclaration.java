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

package com.github.javaparser.symbolsolver.javaparsermodel.declarations;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.javaparsermodel.UnsolvedSymbolException;
import com.github.javaparser.symbolsolver.logic.AbstractTypeDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.*;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceType;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.model.typesystem.Type;
import com.github.javaparser.symbolsolver.resolution.SymbolSolver;

import java.util.*;
import java.util.stream.Collectors;

import static com.github.javaparser.symbolsolver.javaparser.Navigator.getParentNode;

public class JavaParserInterfaceDeclaration extends AbstractTypeDeclaration implements InterfaceDeclaration {

    private TypeSolver typeSolver;
    private ClassOrInterfaceDeclaration wrappedNode;

    public JavaParserInterfaceDeclaration(ClassOrInterfaceDeclaration wrappedNode, TypeSolver typeSolver) {
        if (!wrappedNode.isInterface()) {
            throw new IllegalArgumentException();
        }
        this.wrappedNode = wrappedNode;
        this.typeSolver = typeSolver;
    }

    @Override
    public Set<MethodDeclaration> getDeclaredMethods() {
        Set<MethodDeclaration> methods = new HashSet<>();
        for (BodyDeclaration member : wrappedNode.getMembers()) {
            if (member instanceof com.github.javaparser.ast.body.MethodDeclaration) {
                methods.add(new JavaParserMethodDeclaration((com.github.javaparser.ast.body.MethodDeclaration) member, typeSolver));
            }
        }
        return methods;
    }

    public Context getContext() {
        return JavaParserFactory.getContext(wrappedNode, typeSolver);
    }

    public Type getUsage(Node node) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        JavaParserInterfaceDeclaration that = (JavaParserInterfaceDeclaration) o;

        if (!wrappedNode.equals(that.wrappedNode)) return false;

        return true;
    }

    @Override
    public int hashCode() {
        return wrappedNode.hashCode();
    }

    @Override
    public String getName() {
        return wrappedNode.getName();
    }

    @Override
    public InterfaceDeclaration asInterface() {
        return this;
    }

    @Override
    public boolean hasDirectlyAnnotation(String canonicalName) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isInterface() {
        return true;
    }

    @Override
    public List<ReferenceType> getInterfacesExtended() {
        List<ReferenceType> interfaces = new ArrayList<>();
        if (wrappedNode.getImplements() != null) {
            for (ClassOrInterfaceType t : wrappedNode.getImplements()) {
                interfaces.add(new ReferenceTypeImpl(solveType(t.getName(), typeSolver).getCorrespondingDeclaration().asInterface(), typeSolver));
            }
        }
        return interfaces;
    }

    @Override
    public String getQualifiedName() {
        String containerName = containerName("", getParentNode(wrappedNode));
        if (containerName.isEmpty()) {
            return wrappedNode.getName();
        } else {
            return containerName + "." + wrappedNode.getName();
        }
    }

    @Override
    public boolean isAssignableBy(TypeDeclaration other) {
        List<ReferenceType> ancestorsOfOther = other.getAllAncestors();
        ancestorsOfOther.add(new ReferenceTypeImpl(other, typeSolver));
        for (ReferenceType ancestorOfOther : ancestorsOfOther) {
            if (ancestorOfOther.getQualifiedName().equals(this.getQualifiedName())) {
                return true;
            }
        }
        return false;
    }

    private String containerName(String base, Node container) {
        if (container instanceof ClassOrInterfaceDeclaration) {
            String b = containerName(base, getParentNode(container));
            String cn = ((ClassOrInterfaceDeclaration) container).getName();
            if (b.isEmpty()) {
                return cn;
            } else {
                return b + "." + cn;
            }
        } else if (container instanceof CompilationUnit) {
            Optional<PackageDeclaration> p = ((CompilationUnit) container).getPackage();
            if (p.isPresent()) {
                String b = p.get().getName().toString();
                if (base.isEmpty()) {
                    return b;
                } else {
                    return b + "." + base;
                }
            } else {
                return base;
            }
        } else if (container != null) {
            return containerName(base, getParentNode(container));
        } else {
            return base;
        }
    }

    @Override
    public boolean isAssignableBy(Type type) {
        if (type.isNull()) {
            return true;
        }
        if (type.isReferenceType()) {
            TypeDeclaration other = typeSolver.solveType(type.describe());
            return isAssignableBy(other);
        } else {
            throw new UnsupportedOperationException();
        }
    }

    @Override
    public boolean canBeAssignedTo(TypeDeclaration other) {
        // TODO consider generic types
        if (this.getQualifiedName().equals(other.getQualifiedName())) {
            return true;
        }
        if (this.wrappedNode.getExtends() != null) {
            for (ClassOrInterfaceType type : wrappedNode.getExtends()) {
                TypeDeclaration ancestor = new SymbolSolver(typeSolver).solveType(type);
                if (ancestor.canBeAssignedTo(other)) {
                    return true;
                }
            }
        }

        if (this.wrappedNode.getImplements() != null) {
            for (ClassOrInterfaceType type : wrappedNode.getImplements()) {
                TypeDeclaration ancestor = new SymbolSolver(typeSolver).solveType(type);
                if (ancestor.canBeAssignedTo(other)) {
                    return true;
                }
            }
        }

        return false;
    }

    @Override
    public boolean isTypeParameter() {
        return false;
    }

    @Override
    public FieldDeclaration getField(String name) {
        for (BodyDeclaration member : this.wrappedNode.getMembers()) {
            if (member instanceof com.github.javaparser.ast.body.FieldDeclaration) {
                com.github.javaparser.ast.body.FieldDeclaration field = (com.github.javaparser.ast.body.FieldDeclaration) member;
                for (VariableDeclarator vd : field.getVariables()) {
                    if (vd.getId().getName().equals(name)) {
                        return new JavaParserFieldDeclaration(vd, typeSolver);
                    }
                }
            }
        }

        throw new UnsupportedOperationException("Derived fields");
    }

    @Override
    public List<FieldDeclaration> getAllFields() {
        ArrayList<FieldDeclaration> fields = new ArrayList<>();
        for (BodyDeclaration member : wrappedNode.getMembers()) {
            if (member instanceof com.github.javaparser.ast.body.FieldDeclaration) {
                com.github.javaparser.ast.body.FieldDeclaration field = (com.github.javaparser.ast.body.FieldDeclaration) member;
                for (VariableDeclarator vd : field.getVariables()) {
                    fields.add(new JavaParserFieldDeclaration(vd, typeSolver));
                }
            }
        }

        return fields;
    }


    @Override
    public String toString() {
        return "JavaParserInterfaceDeclaration{" +
                "wrappedNode=" + wrappedNode +
                '}';
    }

    @Override
    public boolean hasField(String name) {
        for (BodyDeclaration member : this.wrappedNode.getMembers()) {
            if (member instanceof com.github.javaparser.ast.body.FieldDeclaration) {
                com.github.javaparser.ast.body.FieldDeclaration field = (com.github.javaparser.ast.body.FieldDeclaration) member;
                for (VariableDeclarator vd : field.getVariables()) {
                    if (vd.getId().getName().equals(name)) {
                        return true;
                    }
                }
            }
        }

        throw new UnsupportedOperationException("Derived fields");
    }

    @Deprecated
    public SymbolReference<TypeDeclaration> solveType(String name, TypeSolver typeSolver) {
        if (this.wrappedNode.getName().equals(name)) {
            return SymbolReference.solved(this);
        }
        if (this.wrappedNode.getTypeParameters() != null) {
            for (com.github.javaparser.ast.type.TypeParameter typeParameter : this.wrappedNode.getTypeParameters()) {
                if (typeParameter.getName().equals(name)) {
                    return SymbolReference.solved(new JavaParserTypeVariableDeclaration(typeParameter, typeSolver));
                }
            }
        }

        // Internal classes
        for (BodyDeclaration member : this.wrappedNode.getMembers()) {
            if (member instanceof com.github.javaparser.ast.body.TypeDeclaration) {
                com.github.javaparser.ast.body.TypeDeclaration internalType = (com.github.javaparser.ast.body.TypeDeclaration) member;
                String prefix = internalType.getName() + ".";
                if (internalType.getName().equals(name)) {
                    if (internalType instanceof ClassOrInterfaceDeclaration) {
                        return SymbolReference.solved(new JavaParserInterfaceDeclaration((ClassOrInterfaceDeclaration) internalType, typeSolver));
                    } else if (internalType instanceof EnumDeclaration) {
                        return SymbolReference.solved(new JavaParserEnumDeclaration((EnumDeclaration) internalType, typeSolver));
                    } else {
                        throw new UnsupportedOperationException();
                    }
                } else if (name.startsWith(prefix) && name.length() > prefix.length()) {
                    if (internalType instanceof ClassOrInterfaceDeclaration) {
                        return new JavaParserInterfaceDeclaration((ClassOrInterfaceDeclaration) internalType, typeSolver).solveType(name.substring(prefix.length()), typeSolver);
                    } else if (internalType instanceof EnumDeclaration) {
                        return new SymbolSolver(typeSolver).solveTypeInType(new JavaParserEnumDeclaration((EnumDeclaration) internalType, typeSolver), name.substring(prefix.length()));
                    } else {
                        throw new UnsupportedOperationException();
                    }
                }
            }
        }

        String prefix = wrappedNode.getName() + ".";
        if (name.startsWith(prefix) && name.length() > prefix.length()) {
            return new JavaParserInterfaceDeclaration(this.wrappedNode, typeSolver).solveType(name.substring(prefix.length()), typeSolver);
        }

        return getContext().getParent().solveType(name, typeSolver);
    }

    @Override
    public List<ReferenceType> getAncestors() {
        List<ReferenceType> ancestors = new ArrayList<>();
        if (wrappedNode.getExtends() != null) {
            for (ClassOrInterfaceType extended : wrappedNode.getExtends()) {
                SymbolReference<TypeDeclaration> ancestor = solveType(extended.getName(), typeSolver);
                if (!ancestor.isSolved()) {
                    throw new UnsolvedSymbolException(extended.getName());
                }
                ancestors.add(new ReferenceTypeImpl(ancestor.getCorrespondingDeclaration(), typeSolver));
            }
        }
        if (wrappedNode.getImplements() != null) {
            for (ClassOrInterfaceType implemented : wrappedNode.getImplements()) {
                SymbolReference<TypeDeclaration> ancestor = solveType(implemented.getName(), typeSolver);
                if (!ancestor.isSolved()) {
                    throw new UnsolvedSymbolException(implemented.getName());
                }
                ancestors.add(new ReferenceTypeImpl(ancestor.getCorrespondingDeclaration(), typeSolver));
            }
        }
        return ancestors;
    }

    @Override
    public List<TypeParameterDeclaration> getTypeParameters() {
        if (this.wrappedNode.getTypeParameters() == null) {
            return Collections.emptyList();
        } else {
            return this.wrappedNode.getTypeParameters().stream().map(
                    (tp) -> new JavaParserTypeParameter(tp, typeSolver)
            ).collect(Collectors.toList());
        }
    }

    /**
     * Returns the JavaParser node associated with this JavaParserInterfaceDeclaration.
     *
     * @return A visitable JavaParser node wrapped by this object.
     */
    public ClassOrInterfaceDeclaration getWrappedNode() {
        return wrappedNode;
    }

    @Override
    public AccessLevel accessLevel() {
        throw new UnsupportedOperationException();
    }
}
