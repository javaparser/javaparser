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

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedParameterDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.core.resolution.TypeVariableResolutionCapability;
import com.github.javaparser.symbolsolver.declarations.common.MethodDeclarationCommonLogic;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import javassist.CtMethod;
import javassist.NotFoundException;
import javassist.bytecode.BadBytecode;
import javassist.bytecode.SignatureAttribute;

import java.lang.reflect.Modifier;
import java.util.*;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
public class JavassistMethodDeclaration implements ResolvedMethodDeclaration, TypeVariableResolutionCapability {
    private CtMethod ctMethod;
    private TypeSolver typeSolver;

    public JavassistMethodDeclaration(CtMethod ctMethod, TypeSolver typeSolver) {
        this.ctMethod = ctMethod;
        this.typeSolver = typeSolver;
    }

    @Override
    public boolean isDefaultMethod() {
        return ctMethod.getDeclaringClass().isInterface() && !isAbstract();
    }

    @Override
    public boolean isStatic() {
        return Modifier.isStatic(ctMethod.getModifiers());
    }

    @Override
    public String toString() {
        return "JavassistMethodDeclaration{" +
                "ctMethod=" + ctMethod +
                '}';
    }

    @Override
    public String getName() {
        return ctMethod.getName();
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
        return false;
    }

    @Override
    public ResolvedReferenceTypeDeclaration declaringType() {
        if (ctMethod.getDeclaringClass().isInterface()) {
            return new JavassistInterfaceDeclaration(ctMethod.getDeclaringClass(), typeSolver);
        } else if (ctMethod.getDeclaringClass().isEnum()) {
            return new JavassistEnumDeclaration(ctMethod.getDeclaringClass(), typeSolver);
        } else {
            return new JavassistClassDeclaration(ctMethod.getDeclaringClass(), typeSolver);
        }
    }

    @Override
    public ResolvedType getReturnType() {
        try {
            if (ctMethod.getGenericSignature() != null) {
                javassist.bytecode.SignatureAttribute.Type genericSignatureType = SignatureAttribute.toMethodSignature(ctMethod.getGenericSignature()).getReturnType();
                return JavassistUtils.signatureTypeToType(genericSignatureType, typeSolver, this);
            } else {
                return JavassistFactory.typeUsageFor(ctMethod.getReturnType(), typeSolver);
            }
        } catch (NotFoundException | BadBytecode e) {
            throw new RuntimeException(e);
        }
    }


    @Override
    public int getNumberOfParams() {
        try {
            return ctMethod.getParameterTypes().length;
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public ResolvedParameterDeclaration getParam(int i) {
        try {
            boolean variadic = false;
            if ((ctMethod.getModifiers() & javassist.Modifier.VARARGS) > 0) {
                variadic = i == (ctMethod.getParameterTypes().length - 1);
            }
            Optional<String> paramName = JavassistUtils.extractParameterName(ctMethod, i);
            String signature = ctMethod.getGenericSignature() == null ? ctMethod.getSignature() : ctMethod.getGenericSignature();
            SignatureAttribute.MethodSignature methodSignature = SignatureAttribute.toMethodSignature(signature);
            SignatureAttribute.Type signatureType = methodSignature.getParameterTypes()[i];
            return new JavassistParameterDeclaration(JavassistUtils.signatureTypeToType(signatureType,
                    typeSolver, this), typeSolver, variadic, paramName.orElse(null));

        } catch (NotFoundException | BadBytecode e) {
            throw new RuntimeException(e);
        }
    }

    public MethodUsage getUsage(Node node) {
        throw new UnsupportedOperationException();
    }

    public MethodUsage resolveTypeVariables(Context context, List<ResolvedType> parameterTypes) {
        return new MethodDeclarationCommonLogic(this, typeSolver).resolveTypeVariables(context, parameterTypes);
    }

    @Override
    public boolean isAbstract() {
        return Modifier.isAbstract(ctMethod.getModifiers());
    }

    @Override
    public List<ResolvedTypeParameterDeclaration> getTypeParameters() {
        try {
            if (ctMethod.getGenericSignature() == null) {
                return new ArrayList<>();
            }
            SignatureAttribute.MethodSignature methodSignature = SignatureAttribute.toMethodSignature(ctMethod.getGenericSignature());
            return Arrays.stream(methodSignature.getTypeParameters()).map((jasTp) -> new JavassistTypeParameter(jasTp, this, typeSolver)).collect(Collectors.toList());
        } catch (BadBytecode badBytecode) {
            throw new RuntimeException(badBytecode);
        }
    }

    @Override
    public AccessSpecifier accessSpecifier() {
        return JavassistFactory.modifiersToAccessLevel(ctMethod.getModifiers());
    }

    @Override
    public int getNumberOfSpecifiedExceptions() {
        try {
            return ctMethod.getExceptionTypes().length;
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public ResolvedType getSpecifiedException(int index) {
        if (index < 0 || index >= getNumberOfSpecifiedExceptions()) {
            throw new IllegalArgumentException(String.format("No exception with index %d. Number of exceptions: %d",
                    index, getNumberOfSpecifiedExceptions()));
        }
        try {
            return JavassistFactory.typeUsageFor(ctMethod.getExceptionTypes()[index], typeSolver);
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public Optional<MethodDeclaration> toAst() {
        return Optional.empty();
    }
}
