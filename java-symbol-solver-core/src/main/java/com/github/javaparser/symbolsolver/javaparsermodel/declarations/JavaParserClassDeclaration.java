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
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.javaparsermodel.UnsolvedSymbolException;
import com.github.javaparser.symbolsolver.logic.AbstractClassDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.*;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceType;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.model.typesystem.Type;
import com.github.javaparser.symbolsolver.resolution.SymbolSolver;
import com.google.common.collect.ImmutableList;

import java.util.*;
import java.util.stream.Collectors;

import static com.github.javaparser.symbolsolver.javaparser.Navigator.getParentNode;

public class JavaParserClassDeclaration extends AbstractClassDeclaration {

    private TypeSolver typeSolver;
    private com.github.javaparser.ast.body.ClassOrInterfaceDeclaration wrappedNode;

    public JavaParserClassDeclaration(com.github.javaparser.ast.body.ClassOrInterfaceDeclaration wrappedNode,
                                      TypeSolver typeSolver) {
        if (wrappedNode.isInterface()) {
            throw new IllegalArgumentException("Interface given");
        }
        this.wrappedNode = wrappedNode;
        this.typeSolver = typeSolver;
    }

    public SymbolReference<MethodDeclaration> solveMethod(String name, List<Type> parameterTypes) {
        Context ctx = getContext();
        return ctx.solveMethod(name, parameterTypes, typeSolver);
    }

    public Context getContext() {
        return JavaParserFactory.getContext(wrappedNode, typeSolver);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        JavaParserClassDeclaration that = (JavaParserClassDeclaration) o;

        if (!wrappedNode.equals(that.wrappedNode)) return false;

        return true;
    }

    @Override
    public int hashCode() {
        return wrappedNode.hashCode();
    }

    public Type getUsage(Node node) {
        throw new UnsupportedOperationException();
    }

    @Override
    public String getName() {
        return wrappedNode.getName();
    }

    @Override
    public boolean isField() {
        return false;
    }

    @Override
    public boolean isParameter() {
        return false;
    }

    @Override
    public boolean isType() {
        return true;
    }

    @Override
    public boolean isClass() {
        return !wrappedNode.isInterface();
    }

    @Override
    public ReferenceTypeImpl getSuperClass() {
        if (wrappedNode.getExtends().isEmpty()) {
            return new ReferenceTypeImpl(typeSolver.getRoot().solveType("java.lang.Object").asType().asClass(), typeSolver);
        } else {
            SymbolReference<TypeDeclaration> ref = solveType(wrappedNode.getExtends().get(0).getName(), typeSolver);
            if (!ref.isSolved()) {
                throw new UnsolvedSymbolException(wrappedNode.getExtends().get(0).getName());
            }
            List<Type> superClassTypeParameters = wrappedNode.getExtends().get(0).getTypeArguments().orElse(new NodeList<>())
                    .stream().map(ta -> JavaParserFacade.get(typeSolver).convert(ta, ta))
                    .collect(Collectors.toList());
            return new ReferenceTypeImpl(ref.getCorrespondingDeclaration().asClass(), superClassTypeParameters, typeSolver);
        }
    }

    @Override
    public List<ReferenceType> getInterfaces() {
        List<ReferenceType> interfaces = new ArrayList<>();
        if (wrappedNode.getImplements() != null) {
            for (ClassOrInterfaceType t : wrappedNode.getImplements()) {
                List<Type> interfaceTypeParameters = t.getTypeArguments().orElse(new NodeList<>())
                        .stream().map(ta -> JavaParserFacade.get(typeSolver).convert(ta, ta))
                        .collect(Collectors.toList());
                ReferenceType referenceType = new ReferenceTypeImpl(solveType(t.getName(), typeSolver).getCorrespondingDeclaration().asType().asInterface(),
                        interfaceTypeParameters,
                        typeSolver);
                interfaces.add(referenceType);
            }
        }
        return interfaces;
    }

    @Override
    public List<ConstructorDeclaration> getConstructors() {
        List<ConstructorDeclaration> declared = new LinkedList<>();
        for (BodyDeclaration member : wrappedNode.getMembers()) {
            if (member instanceof com.github.javaparser.ast.body.ConstructorDeclaration) {
                com.github.javaparser.ast.body.ConstructorDeclaration constructorDeclaration = (com.github.javaparser.ast.body.ConstructorDeclaration) member;
                declared.add(new JavaParserConstructorDeclaration(this, constructorDeclaration, typeSolver));
            }
        }
        if (declared.isEmpty()) {
            // If there are no constructors insert the default constructor
            return ImmutableList.of(new DefaultConstructorDeclaration(this));
        } else {
            return declared;
        }
    }

    public ClassDeclaration asClass() {
        return this;
    }

    @Override
    public boolean hasDirectlyAnnotation(String canonicalName) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isInterface() {
        return wrappedNode.isInterface();
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
        if (container instanceof com.github.javaparser.ast.body.ClassOrInterfaceDeclaration) {
            String b = containerName(base, getParentNode(container));
            String cn = ((com.github.javaparser.ast.body.ClassOrInterfaceDeclaration) container).getName();
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
        ClassDeclaration superclass = (ClassDeclaration) getSuperClass().getTypeDeclaration();
        if (superclass != null && superclass.canBeAssignedTo(other)) {
            return true;
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

        ClassDeclaration superclass = (ClassDeclaration) this.getSuperClass().getTypeDeclaration();
        if (superclass != null) {
            return superclass.getField(name);
        } else {
            throw new UnsolvedSymbolException("In class " + this, name);
        }

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

        ClassDeclaration superclass = (ClassDeclaration) this.getSuperClass().getTypeDeclaration();
        fields.addAll(superclass.getAllFields());

        return fields;
    }

    @Override
    public String toString() {
        return "JavaParserClassDeclaration{" +
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

        ClassDeclaration superclass = (ClassDeclaration) this.getSuperClass().getTypeDeclaration();
        if (superclass != null) {
            return superclass.hasField(name);
        } else {
            return false;
        }
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
                        return SymbolReference.solved(new JavaParserClassDeclaration((com.github.javaparser.ast.body.ClassOrInterfaceDeclaration) internalType, typeSolver));
                    } else if (internalType instanceof EnumDeclaration) {
                        return SymbolReference.solved(new JavaParserEnumDeclaration((com.github.javaparser.ast.body.EnumDeclaration) internalType, typeSolver));
                    } else {
                        throw new UnsupportedOperationException();
                    }
                } else if (name.startsWith(prefix) && name.length() > prefix.length()) {
                    if (internalType instanceof ClassOrInterfaceDeclaration) {
                        return new JavaParserClassDeclaration((com.github.javaparser.ast.body.ClassOrInterfaceDeclaration) internalType, typeSolver).solveType(name.substring(prefix.length()), typeSolver);
                    } else if (internalType instanceof EnumDeclaration) {
                        return new SymbolSolver(typeSolver).solveTypeInType(new JavaParserEnumDeclaration((com.github.javaparser.ast.body.EnumDeclaration) internalType, typeSolver), name.substring(prefix.length()));
                    } else {
                        throw new UnsupportedOperationException();
                    }
                }
            }
        }

        String prefix = wrappedNode.getName() + ".";
        if (name.startsWith(prefix) && name.length() > prefix.length()) {
            return new JavaParserClassDeclaration(this.wrappedNode, typeSolver).solveType(name.substring(prefix.length()), typeSolver);
        }

        return getContext().getParent().solveType(name, typeSolver);
    }

    @Override
    public List<ReferenceType> getAncestors() {
        List<ReferenceType> ancestors = new ArrayList<>();
        ReferenceTypeImpl superclass = getSuperClass();
        if (superclass != null) {
            ancestors.add(superclass);
        }
        if (wrappedNode.getImplements() != null) {
            for (ClassOrInterfaceType implemented : wrappedNode.getImplements()) {
                ReferenceTypeImpl ancestor = toTypeUsage(implemented, typeSolver);
                ancestors.add(ancestor);
            }
        }
        return ancestors;
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

    private ReferenceTypeImpl toTypeUsage(ClassOrInterfaceType type, TypeSolver typeSolver) {
        SymbolReference<TypeDeclaration> ancestor = solveType(type.getName(), typeSolver.getRoot());
        if (!ancestor.isSolved()) {
            throw new UnsolvedSymbolException(type.getName());
        }
        if (type.getTypeArguments().isPresent()) {
            List<Type> typeParams = type.getTypeArguments().get().stream().map((t) -> toTypeUsage(t, typeSolver)).collect(Collectors.toList());
            return new ReferenceTypeImpl(ancestor.getCorrespondingDeclaration(), typeParams, typeSolver);
        } else {
            return new ReferenceTypeImpl(ancestor.getCorrespondingDeclaration(), typeSolver);
        }
    }

    private Type toTypeUsage(com.github.javaparser.ast.type.Type type, TypeSolver typeSolver) {
        return JavaParserFacade.get(typeSolver).convert(type, type);
    }

    @Override
    public List<TypeParameterDeclaration> getTypeParameters() {
        return this.wrappedNode.getTypeParameters().stream().map(
                (tp) -> new JavaParserTypeParameter(tp, typeSolver)
        ).collect(Collectors.toList());
    }

    @Override
    protected ReferenceType object() {
        return new ReferenceTypeImpl(typeSolver.solveType(Object.class.getCanonicalName()), typeSolver);
    }

    /**
     * Returns the JavaParser node associated with this JavaParserClassDeclaration.
     *
     * @return A visitable JavaParser node wrapped by this object.
     */
    public com.github.javaparser.ast.body.ClassOrInterfaceDeclaration getWrappedNode() {
        return wrappedNode;
    }

    @Override
    public AccessLevel accessLevel() {
        throw new UnsupportedOperationException();
    }
}
