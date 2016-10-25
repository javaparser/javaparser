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
import com.github.javaparser.ast.body.EnumConstantDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.javaparsermodel.UnsolvedSymbolException;
import com.github.javaparser.symbolsolver.logic.AbstractTypeDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.*;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.methods.MethodUsage;
import com.github.javaparser.symbolsolver.model.typesystem.parametrization.TypeParametersMap;
import com.github.javaparser.symbolsolver.model.typesystem.ArrayType;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceType;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.model.typesystem.Type;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionFactory;
import com.github.javaparser.symbolsolver.resolution.SymbolSolver;

import java.io.Serializable;
import java.util.*;

import static com.github.javaparser.symbolsolver.javaparser.Navigator.getParentNode;

public class JavaParserEnumDeclaration extends AbstractTypeDeclaration implements EnumDeclaration {

    private TypeSolver typeSolver;
    private com.github.javaparser.ast.body.EnumDeclaration wrappedNode;

    public JavaParserEnumDeclaration(com.github.javaparser.ast.body.EnumDeclaration wrappedNode, TypeSolver typeSolver) {
        this.wrappedNode = wrappedNode;
        this.typeSolver = typeSolver;
    }

    @Override
    public String toString() {
        return "JavaParserEnumDeclaration{" +
                "wrappedNode=" + wrappedNode +
                '}';
    }

    @Override
    public boolean isAssignableBy(TypeDeclaration other) {
        return isAssignableBy(new ReferenceTypeImpl(other, typeSolver));
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
    public boolean hasDirectlyAnnotation(String canonicalName) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean canBeAssignedTo(TypeDeclaration other) {
        // Enums cannot be extended
        if (other.getQualifiedName().equals(this.getQualifiedName())) {
            return true;
        }
        if (other.getQualifiedName().equals(Enum.class.getCanonicalName())) {
            return true;
        }
        // Enum implements Comparable and Serializable
        if (other.getQualifiedName().equals(Comparable.class.getCanonicalName())) {
            return true;
        }
        if (other.getQualifiedName().equals(Serializable.class.getCanonicalName())) {
            return true;
        }
        if (other.getQualifiedName().equals(Object.class.getCanonicalName())) {
            return true;
        }
        return false;
    }

    @Override
    public boolean isClass() {
        return false;
    }

    @Override
    public boolean isInterface() {
        return false;
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
        return type.isReferenceType() && type.asReferenceType().getQualifiedName().equals(getQualifiedName());
    }


    @Override
    public boolean isTypeParameter() {
        return false;
    }

    @Override
    public FieldDeclaration getField(String name) {
        if (this.wrappedNode.getMembers() != null) {
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
        }

        if (this.wrappedNode.getEntries() != null) {
            for (EnumConstantDeclaration member : this.wrappedNode.getEntries()) {
                if (member.getName().equals(name)) {
                    return new JavaParserFieldDeclaration(member, typeSolver);
                }
            }
        }

        throw new UnsolvedSymbolException("Field " + name);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        JavaParserEnumDeclaration that = (JavaParserEnumDeclaration) o;

        if (!wrappedNode.equals(that.wrappedNode)) return false;

        return true;
    }

    @Override
    public int hashCode() {
        return wrappedNode.hashCode();
    }

    @Deprecated
    public Optional<MethodUsage> solveMethodAsUsage(String name, List<Type> parameterTypes, TypeSolver typeSolver, Context invokationContext, List<Type> typeParameterValues) {
        if (name.equals("values") && parameterTypes.isEmpty()) {
            return Optional.of(new ValuesMethod(this, typeSolver).getUsage(null));
        }
        // TODO add methods inherited from Enum
        return getContext().solveMethodAsUsage(name, parameterTypes, typeSolver);
    }

    @Override
    public boolean hasField(String name) {
        if (this.wrappedNode.getMembers() != null) {
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

        }

        if (this.wrappedNode.getEntries() != null) {
            for (EnumConstantDeclaration member : this.wrappedNode.getEntries()) {
                if (member.getName().equals(name)) {
                    return true;
                }
            }
        }

        return false;
    }

    @Override
    public List<FieldDeclaration> getAllFields() {
        ArrayList<FieldDeclaration> fields = new ArrayList<>();
        if (this.wrappedNode.getMembers() != null) {
            for (BodyDeclaration member : this.wrappedNode.getMembers()) {
                if (member instanceof com.github.javaparser.ast.body.FieldDeclaration) {
                    com.github.javaparser.ast.body.FieldDeclaration field = (com.github.javaparser.ast.body.FieldDeclaration) member;
                    for (VariableDeclarator vd : field.getVariables()) {
                        fields.add(new JavaParserFieldDeclaration(vd, typeSolver));
                    }
                }
            }
        }

        if (this.wrappedNode.getEntries() != null) {
            for (EnumConstantDeclaration member : this.wrappedNode.getEntries()) {
                fields.add(new JavaParserFieldDeclaration(member, typeSolver));
            }
        }

        return fields;
    }

    @Override
    public List<ReferenceType> getAncestors() {
        List<ReferenceType> ancestors = new ArrayList<>();
        ReferenceType enumClass = ReflectionFactory.typeUsageFor(Enum.class, typeSolver).asReferenceType();
        TypeParameterDeclaration eTypeParameter = enumClass.getTypeDeclaration().getTypeParameters().get(0);
        enumClass = enumClass.deriveTypeParameters(new TypeParametersMap.Builder().setValue(eTypeParameter, new ReferenceTypeImpl(this, typeSolver)).build());
        ancestors.add(enumClass);
        if (wrappedNode.getImplements() != null) {
            for (ClassOrInterfaceType implementedType : wrappedNode.getImplements()) {
                SymbolReference<TypeDeclaration> implementedDeclRef = new SymbolSolver(typeSolver).solveTypeInType(this, implementedType.getName());
                if (!implementedDeclRef.isSolved()) {
                    throw new UnsolvedSymbolException(implementedType.getName());
                }
                ancestors.add(new ReferenceTypeImpl(implementedDeclRef.getCorrespondingDeclaration(), typeSolver));
            }
        }
        return ancestors;
    }

    @Override
    public List<TypeParameterDeclaration> getTypeParameters() {
        return Collections.emptyList();
    }

    /**
     * Returns the JavaParser node associated with this JavaParserEnumDeclaration.
     *
     * @return A visitable JavaParser node wrapped by this object.
     */
    public com.github.javaparser.ast.body.EnumDeclaration getWrappedNode() {
        return wrappedNode;
    }

    // Needed by ContextHelper
    public static class ValuesMethod implements MethodDeclaration {

        private JavaParserEnumDeclaration enumDeclaration;
        private TypeSolver typeSolver;

        public ValuesMethod(JavaParserEnumDeclaration enumDeclaration, TypeSolver typeSolver) {
            this.enumDeclaration = enumDeclaration;
            this.typeSolver = typeSolver;
        }

        @Override
        public TypeDeclaration declaringType() {
            return enumDeclaration;
        }

        @Override
        public Type getReturnType() {
            return new ArrayType(new ReferenceTypeImpl(enumDeclaration, typeSolver));
        }

        @Override
        public int getNumberOfParams() {
            return 0;
        }

        @Override
        public ParameterDeclaration getParam(int i) {
            throw new UnsupportedOperationException();
        }

        public MethodUsage getUsage(Node node) {
            throw new UnsupportedOperationException();
        }

        public MethodUsage resolveTypeVariables(Context context, List<Type> parameterTypes) {
            return new MethodUsage(this);
        }

        @Override
        public boolean isAbstract() {
            throw new UnsupportedOperationException();
        }

        @Override
        public boolean isDefaultMethod() {
            return false;
        }

        @Override
        public String getName() {
            return "values";
        }

        @Override
        public List<TypeParameterDeclaration> getTypeParameters() {
            return Collections.emptyList();
        }

        @Override
        public AccessLevel accessLevel() {
            throw new UnsupportedOperationException();
        }
    }

    @Override
    public AccessLevel accessLevel() {
        throw new UnsupportedOperationException();
    }
}
