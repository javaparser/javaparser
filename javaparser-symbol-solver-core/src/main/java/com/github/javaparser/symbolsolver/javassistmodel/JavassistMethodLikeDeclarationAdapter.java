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

package com.github.javaparser.symbolsolver.javassistmodel;

import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedMethodLikeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedParameterDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedType;
import javassist.CtBehavior;
import javassist.bytecode.BadBytecode;
import javassist.bytecode.ExceptionsAttribute;
import javassist.bytecode.SignatureAttribute;

import java.util.*;
import java.util.stream.Collectors;

public class JavassistMethodLikeDeclarationAdapter {

    private CtBehavior ctBehavior;
    private TypeSolver typeSolver;
    private ResolvedMethodLikeDeclaration declaration;

    private SignatureAttribute.MethodSignature methodSignature;

    public JavassistMethodLikeDeclarationAdapter(CtBehavior ctBehavior, TypeSolver typeSolver, ResolvedMethodLikeDeclaration declaration) {
        this.ctBehavior = ctBehavior;
        this.typeSolver = typeSolver;
        this.declaration = declaration;

        try {
            String signature = ctBehavior.getGenericSignature();
            if (signature == null) {
                signature = ctBehavior.getSignature();
            }
            methodSignature = SignatureAttribute.toMethodSignature(signature);
        } catch (BadBytecode e) {
            throw new RuntimeException(e);
        }
    }

    public int getNumberOfParams() {
        return methodSignature.getParameterTypes().length;
    }

    public ResolvedParameterDeclaration getParam(int i) {
        boolean variadic = false;
        if ((ctBehavior.getModifiers() & javassist.Modifier.VARARGS) > 0) {
            variadic = i == (methodSignature.getParameterTypes().length - 1);
        }

        Optional<String> paramName = JavassistUtils.extractParameterName(ctBehavior, i);
        ResolvedType type = JavassistUtils.signatureTypeToType(methodSignature.getParameterTypes()[i], typeSolver, declaration);
        return new JavassistParameterDeclaration(type, typeSolver, variadic, paramName.orElse(null));
    }

    public List<ResolvedTypeParameterDeclaration> getTypeParameters() {
        if (ctBehavior.getGenericSignature() == null) {
            return new ArrayList<>();
        }
        return Arrays.stream(methodSignature.getTypeParameters())
                .map(jasTp -> new JavassistTypeParameter(jasTp, declaration, typeSolver))
                .collect(Collectors.toList());
    }

    public int getNumberOfSpecifiedExceptions() {
        ExceptionsAttribute exceptionsAttribute = ctBehavior.getMethodInfo().getExceptionsAttribute();
        if (exceptionsAttribute == null) {
            return 0;
        }

        String[] exceptions = exceptionsAttribute.getExceptions();
        return exceptions == null ? 0 : exceptions.length;
    }

    public ResolvedType getSpecifiedException(int index) {
        if (index < 0) {
            throw new IllegalArgumentException(String.format("index < 0: %d", index));
        }

        ExceptionsAttribute exceptionsAttribute = ctBehavior.getMethodInfo().getExceptionsAttribute();
        if (exceptionsAttribute == null) {
            throw new IllegalArgumentException(String.format("No exception with index %d. Number of exceptions: 0", index));
        }

        String[] exceptions = exceptionsAttribute.getExceptions();
        if (exceptions == null || index >= exceptions.length) {
            throw new IllegalArgumentException(String.format("No exception with index %d. Number of exceptions: %d",
                    index, getNumberOfSpecifiedExceptions()));
        }

        ResolvedReferenceTypeDeclaration typeDeclaration = typeSolver.solveType(exceptions[index]);
        return new ReferenceTypeImpl(typeDeclaration, Collections.emptyList());
    }

    public ResolvedType getReturnType() {
        return JavassistUtils.signatureTypeToType(methodSignature.getReturnType(), typeSolver, declaration);
    }
}
