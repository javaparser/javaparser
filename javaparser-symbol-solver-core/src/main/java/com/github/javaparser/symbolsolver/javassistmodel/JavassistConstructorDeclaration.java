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
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import javassist.CtConstructor;
import javassist.NotFoundException;
import javassist.bytecode.*;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * @author Fred Lefévère-Laoide
 */
public class JavassistConstructorDeclaration implements ResolvedConstructorDeclaration {
    private final CtConstructor ctConstructor;
    private final TypeSolver typeSolver;

    public JavassistConstructorDeclaration(CtConstructor ctConstructor, TypeSolver typeSolver) {
        this.ctConstructor = ctConstructor;
        this.typeSolver = typeSolver;
    }

    @Override
    public String toString() {
        return getClass().getSimpleName() + "{" +
                "ctConstructor=" + ctConstructor.getName() +
                ", typeSolver=" + typeSolver +
                '}';
    }

    @Override
    public String getName() {
        return ctConstructor.getName();
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
    public ResolvedClassDeclaration declaringType() {
        return new JavassistClassDeclaration(ctConstructor.getDeclaringClass(), typeSolver);
    }

    @Override
    public int getNumberOfParams() {
        try {
            return ctConstructor.getParameterTypes().length;
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public ResolvedParameterDeclaration getParam(int i) {
        try {
            boolean variadic = false;
            if ((ctConstructor.getModifiers() & javassist.Modifier.VARARGS) > 0) {
                variadic = i == (ctConstructor.getParameterTypes().length - 1);
            }
            Optional<String> paramName = JavassistUtils.extractParameterName(ctConstructor, i);
            if (ctConstructor.getGenericSignature() != null) {
                SignatureAttribute.MethodSignature methodSignature = SignatureAttribute.toMethodSignature(ctConstructor.getGenericSignature());
                SignatureAttribute.Type signatureType = methodSignature.getParameterTypes()[i];
                return new JavassistParameterDeclaration(JavassistUtils.signatureTypeToType(signatureType,
                        typeSolver, this), typeSolver, variadic, paramName.orElse(null));
            } else {
                return new JavassistParameterDeclaration(ctConstructor.getParameterTypes()[i], typeSolver, variadic,
                        paramName.orElse(null));
            }
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        } catch (BadBytecode badBytecode) {
            throw new RuntimeException(badBytecode);
        }
    }

    @Override
    public List<ResolvedTypeParameterDeclaration> getTypeParameters() {
        try {
            if (ctConstructor.getGenericSignature() == null) {
                return Collections.emptyList();
            }
            SignatureAttribute.MethodSignature methodSignature = SignatureAttribute.toMethodSignature(ctConstructor.getGenericSignature());
            return Arrays.stream(methodSignature.getTypeParameters()).map((jasTp) -> new JavassistTypeParameter(jasTp, this, typeSolver)).collect(Collectors.toList());
        } catch (BadBytecode badBytecode) {
            throw new RuntimeException(badBytecode);
        }
    }

    @Override
    public AccessSpecifier accessSpecifier() {
        return JavassistFactory.modifiersToAccessLevel(ctConstructor.getModifiers());
    }

    @Override
    public int getNumberOfSpecifiedExceptions() {
        try {
            return ctConstructor.getExceptionTypes().length;
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
            return JavassistFactory.typeUsageFor(ctConstructor.getExceptionTypes()[index], typeSolver);
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public Optional<ConstructorDeclaration> toAst() {
        return Optional.empty();
    }
}
