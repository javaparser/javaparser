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

package com.github.javaparser.symbolsolver.javassistmodel;

import com.github.javaparser.ast.Node;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparsermodel.LambdaArgumentTypePlaceholder;
import com.github.javaparser.symbolsolver.logic.AbstractClassDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.*;
import com.github.javaparser.symbolsolver.model.methods.MethodUsage;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceType;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.model.typesystem.Type;
import com.github.javaparser.symbolsolver.resolution.MethodResolutionLogic;
import javassist.CtClass;
import javassist.CtField;
import javassist.CtMethod;
import javassist.NotFoundException;
import javassist.bytecode.BadBytecode;
import javassist.bytecode.SignatureAttribute;

import java.util.*;
import java.util.stream.Collectors;

public class JavassistClassDeclaration extends AbstractClassDeclaration {

    private CtClass ctClass;
    private TypeSolver typeSolver;

    @Override
    protected ReferenceType object() {
        return new ReferenceTypeImpl(typeSolver.solveType(Object.class.getCanonicalName()), typeSolver);
    }

    @Override
    public ClassDeclaration asClass() {
        return this;
    }

    @Override
    public boolean hasDirectlyAnnotation(String canonicalName) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Set<MethodDeclaration> getDeclaredMethods() {
        return Arrays.stream(ctClass.getDeclaredMethods())
                .map(m -> new JavassistMethodDeclaration(m, typeSolver))
                .collect(Collectors.toSet());
    }

    public JavassistClassDeclaration(CtClass ctClass, TypeSolver typeSolver) {
        if (ctClass == null) {
            throw new IllegalArgumentException();
        }
        if (ctClass.isInterface() || ctClass.isAnnotation() || ctClass.isPrimitive() || ctClass.isEnum()) {
            throw new IllegalArgumentException("Trying to instantiate a JavassistClassDeclaration with something which is not a class: " + ctClass.toString());
        }
        this.ctClass = ctClass;
        this.typeSolver = typeSolver;
    }

    @Override
    public boolean isAssignableBy(TypeDeclaration other) {
        return isAssignableBy(new ReferenceTypeImpl(other, typeSolver));
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        JavassistClassDeclaration that = (JavassistClassDeclaration) o;

        if (!ctClass.equals(that.ctClass)) return false;

        return true;
    }

    @Override
    public int hashCode() {
        return ctClass.hashCode();
    }

    @Override
    public String getQualifiedName() {
        return ctClass.getName();
    }

    public Optional<MethodUsage> solveMethodAsUsage(String name, List<Type> argumentsTypes, TypeSolver typeSolver,
                                                    Context invokationContext, List<Type> typeParameterValues) {
        return JavassistUtils.getMethodUsage(ctClass, name, argumentsTypes, typeSolver, invokationContext);
    }

    @Deprecated
    public SymbolReference<? extends ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        for (CtField field : ctClass.getDeclaredFields()) {
            if (field.getName().equals(name)) {
                return SymbolReference.solved(new JavassistFieldDeclaration(field, typeSolver));
            }
        }

        try {
            CtClass superClass = ctClass.getSuperclass();
            if (superClass != null) {
                SymbolReference<? extends ValueDeclaration> ref = new JavassistClassDeclaration(superClass, typeSolver).solveSymbol(name, typeSolver);
                if (ref.isSolved()) {
                    return ref;
                }
            }
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }

        try {
            for (CtClass interfaze : ctClass.getInterfaces()) {
                SymbolReference<? extends ValueDeclaration> ref = new JavassistInterfaceDeclaration(interfaze, typeSolver).solveSymbol(name, typeSolver);
                if (ref.isSolved()) {
                    return ref;
                }
            }
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }

        return SymbolReference.unsolved(ValueDeclaration.class);
    }

    @Override
    public List<ReferenceType> getAncestors() {
        List<ReferenceType> ancestors = new LinkedList<>();
        if (getSuperClass() != null) {
            ancestors.add(getSuperClass());
        }
        ancestors.addAll(getInterfaces());
        return ancestors;
    }

    public Context getContext() {
        throw new UnsupportedOperationException();
    }

    @Deprecated
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<Type> argumentsTypes) {
        List<MethodDeclaration> candidates = new ArrayList<>();
        for (CtMethod method : ctClass.getDeclaredMethods()) {
            // TODO avoid bridge and synthetic methods
            if (method.getName().equals(name)) {
                candidates.add(new JavassistMethodDeclaration(method, typeSolver));
            }
        }

        try {
            CtClass superClass = ctClass.getSuperclass();
            if (superClass != null) {
                SymbolReference<MethodDeclaration> ref = new JavassistClassDeclaration(superClass, typeSolver).solveMethod(name, argumentsTypes);
                if (ref.isSolved()) {
                    candidates.add(ref.getCorrespondingDeclaration());
                }
            }
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }

        try {
            for (CtClass interfaze : ctClass.getInterfaces()) {
                SymbolReference<MethodDeclaration> ref = new JavassistInterfaceDeclaration(interfaze, typeSolver).solveMethod(name, argumentsTypes);
                if (ref.isSolved()) {
                    candidates.add(ref.getCorrespondingDeclaration());
                }
            }
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }

        return MethodResolutionLogic.findMostApplicable(candidates, name, argumentsTypes, typeSolver);
    }

    public Type getUsage(Node node) {
        return new ReferenceTypeImpl(this, typeSolver);
    }

    @Override
    public boolean isAssignableBy(Type type) {
        if (type.isNull()) {
            return true;
        }

        if (type instanceof LambdaArgumentTypePlaceholder) {
            return isFunctionalInterface();
        }

        // TODO look into generics
        if (type.describe().equals(this.getQualifiedName())) {
            return true;
        }
        try {
            if (this.ctClass.getSuperclass() != null
                    && new JavassistClassDeclaration(this.ctClass.getSuperclass(), typeSolver).isAssignableBy(type)) {
                return true;
            }
            for (CtClass interfaze : ctClass.getInterfaces()) {
                if (new JavassistInterfaceDeclaration(interfaze, typeSolver).isAssignableBy(type)) {
                    return true;
                }
            }
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }
        return false;
    }

    @Override
    public boolean isTypeParameter() {
        return false;
    }

    @Override
    public FieldDeclaration getField(String name) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean hasField(String name) {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<FieldDeclaration> getAllFields() {
        throw new UnsupportedOperationException();
    }

    @Override
    public String getName() {
        return ctClass.getSimpleName();
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
        return !ctClass.isInterface();
    }

    @Override
    public ReferenceType getSuperClass() {
        try {
            if (ctClass.getSuperclass() == null) {
                return new ReferenceTypeImpl(typeSolver.solveType(Object.class.getCanonicalName()), typeSolver);
            }
            if (ctClass.getGenericSignature() == null) {
                return new ReferenceTypeImpl(new JavassistClassDeclaration(ctClass.getSuperclass(), typeSolver), typeSolver);
            }

            SignatureAttribute.ClassSignature classSignature = SignatureAttribute.toClassSignature(ctClass.getGenericSignature());
            return JavassistUtils.signatureTypeToType(classSignature.getSuperClass(), typeSolver, this).asReferenceType();
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        } catch (BadBytecode e) {
           throw new RuntimeException(e);
        }
    }

    @Override
    public List<ReferenceType> getInterfaces() {
        try {
            if (ctClass.getGenericSignature() == null) {
                return Arrays.stream(ctClass.getInterfaces())
                        .map(i -> new JavassistInterfaceDeclaration(i, typeSolver))
                        .map(i -> new ReferenceTypeImpl(i, typeSolver))
                        .collect(Collectors.toList());
            } else {
                SignatureAttribute.ClassSignature classSignature = SignatureAttribute.toClassSignature(ctClass.getGenericSignature());
                return Arrays.stream(classSignature.getInterfaces())
                        .map(i -> JavassistUtils.signatureTypeToType(i, typeSolver, this).asReferenceType())
                        .collect(Collectors.toList());
            }
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        } catch (BadBytecode e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public boolean isInterface() {
        return ctClass.isInterface();
    }

    @Override
    public String toString() {
        return "JavassistClassDeclaration {" + ctClass.getName() + '}';
    }

    @Override
    public List<TypeParameterDeclaration> getTypeParameters() {
        if (null == ctClass.getGenericSignature()) {
            return Collections.emptyList();
        } else {
            try {
                SignatureAttribute.ClassSignature classSignature = SignatureAttribute.toClassSignature(ctClass.getGenericSignature());
                String qualifier = ctClass.getName();
                return Arrays.<SignatureAttribute.TypeParameter>stream(classSignature.getParameters()).map((tp) -> new JavassistTypeParameter(tp, true, qualifier, typeSolver)).collect(Collectors.toList());
            } catch (BadBytecode badBytecode) {
                throw new RuntimeException(badBytecode);
            }
        }
    }

    @Override
    public AccessLevel accessLevel() {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<ConstructorDeclaration> getConstructors() {
        throw new UnsupportedOperationException();
    }

    @Override
    public Optional<TypeDeclaration> containerType() {
        try {
            if (ctClass.getDeclaringClass() == null) {
                return Optional.empty();
            } else {
                throw new UnsupportedOperationException();
            }
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }
    }
}
