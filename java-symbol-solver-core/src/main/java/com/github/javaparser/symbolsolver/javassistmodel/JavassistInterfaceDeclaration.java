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

import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.logic.AbstractTypeDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.*;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.methods.MethodUsage;
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

public class JavassistInterfaceDeclaration extends AbstractTypeDeclaration implements InterfaceDeclaration {

    private CtClass ctClass;

    @Override
    public String toString() {
        return "JavassistInterfaceDeclaration{" +
                "ctClass=" + ctClass.getName() +
                ", typeSolver=" + typeSolver +
                '}';
    }

    private TypeSolver typeSolver;

    public JavassistInterfaceDeclaration(CtClass ctClass, TypeSolver typeSolver) {
        this.ctClass = ctClass;
        this.typeSolver = typeSolver;
        if (!ctClass.isInterface()) {
            throw new IllegalArgumentException("Not an interface: " + ctClass.getName());
        }
    }

    @Override
    public List<ReferenceType> getInterfacesExtended() {
        try {
            return Arrays.stream(ctClass.getInterfaces()).map(i -> new JavassistInterfaceDeclaration(i, typeSolver))
                    .map(i -> new ReferenceTypeImpl(i, typeSolver)).collect(Collectors.toList());
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public String getQualifiedName() {
        return ctClass.getName();
    }

    public Context getContext() {
        throw new UnsupportedOperationException();
    }

    @Deprecated
    public Optional<MethodUsage> solveMethodAsUsage(String name, List<Type> argumentsTypes, TypeSolver typeSolver,
                                                    Context invokationContext, List<Type> typeParameterValues) {

        return JavassistUtils.getMethodUsage(ctClass, name, argumentsTypes, typeSolver, invokationContext);
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

    @Override
    public boolean isAssignableBy(Type type) {
        throw new UnsupportedOperationException();
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
    public boolean isAssignableBy(TypeDeclaration other) {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<ReferenceType> getAncestors() {
        List<ReferenceType> ancestors = new ArrayList<>();
        try {
            for (CtClass interfaze : ctClass.getInterfaces()) {
                ReferenceType superInterfaze = JavassistFactory.typeUsageFor(interfaze, typeSolver).asReferenceType();
                ancestors.add(superInterfaze);
            }
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }
        ancestors = ancestors.stream().filter(a -> a.getQualifiedName() != Object.class.getCanonicalName())
                .collect(Collectors.toList());
        ancestors.add(new ReferenceTypeImpl(typeSolver.solveType(Object.class.getCanonicalName()), typeSolver));
        return ancestors;
    }

    @Override
    public Set<MethodDeclaration> getDeclaredMethods() {
        return Arrays.stream(ctClass.getDeclaredMethods())
                .map(m -> new JavassistMethodDeclaration(m, typeSolver))
                .collect(Collectors.toSet());
    }

    @Override
    public boolean hasDirectlyAnnotation(String canonicalName) {
        try {
            for (Object annotationRaw : ctClass.getAnnotations()) {
                if (annotationRaw.getClass().getCanonicalName().equals(canonicalName)) {
                    return true;
                }
                if (Arrays.stream(annotationRaw.getClass().getInterfaces()).anyMatch(it -> it.getCanonicalName().equals(canonicalName))) {
                    return true;
                }
            }
        } catch (ClassNotFoundException e) {
            throw new RuntimeException(e);
        }
        return false;
    }

    @Override
    public String getName() {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<TypeParameterDeclaration> getTypeParameters() {
        if (null == ctClass.getGenericSignature()) {
            return Collections.emptyList();
        } else {
            try {
                SignatureAttribute.ClassSignature classSignature = SignatureAttribute.toClassSignature(ctClass.getGenericSignature());
                return Arrays.<SignatureAttribute.TypeParameter>stream(classSignature.getParameters()).map((tp) -> new JavassistTypeParameter(tp, true, ctClass.getName(), typeSolver)).collect(Collectors.toList());
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
    public InterfaceDeclaration asInterface() {
        return this;
    }


    @Deprecated
    public SymbolReference<? extends ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        for (CtField field : ctClass.getDeclaredFields()) {
            if (field.getName().equals(name)) {
                return SymbolReference.solved(new JavassistFieldDeclaration(field, typeSolver));
            }
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

}
