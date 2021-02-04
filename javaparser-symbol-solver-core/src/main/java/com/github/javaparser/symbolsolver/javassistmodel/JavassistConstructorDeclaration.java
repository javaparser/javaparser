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

package com.github.javaparser.symbolsolver.javassistmodel;

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.resolution.declarations.ResolvedClassDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedParameterDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import javassist.CtConstructor;
import javassist.NotFoundException;
import javassist.bytecode.BadBytecode;
import javassist.bytecode.SignatureAttribute;

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
    public Optional<Node> toAst() {
        return Optional.empty();
    }
}
