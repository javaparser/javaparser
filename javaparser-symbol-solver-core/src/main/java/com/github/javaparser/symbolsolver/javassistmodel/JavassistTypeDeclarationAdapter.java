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

import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedFieldDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.LambdaArgumentTypePlaceholder;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import javassist.CtClass;
import javassist.CtField;
import javassist.NotFoundException;
import javassist.bytecode.AccessFlag;
import javassist.bytecode.BadBytecode;
import javassist.bytecode.SignatureAttribute;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * @author Federico Tomassetti
 */
public class JavassistTypeDeclarationAdapter {

    private CtClass ctClass;
    private TypeSolver typeSolver;
    private ResolvedReferenceTypeDeclaration typeDeclaration;

    public JavassistTypeDeclarationAdapter(CtClass ctClass, TypeSolver typeSolver, ResolvedReferenceTypeDeclaration typeDeclaration) {
        this.ctClass = ctClass;
        this.typeSolver = typeSolver;
        this.typeDeclaration = typeDeclaration;
    }

    public Optional<ResolvedReferenceType> getSuperClass() {
        try {
            if ("java.lang.Object".equals(ctClass.getClassFile().getName())) {
                // If this is java.lang.Object, ignore the presence of any superclass (preventing any infinite loops).
                return Optional.empty();
            }
            if (ctClass.getGenericSignature() == null) {
                // Compiled classes have generic types erased, but can be made available for reflection via getGenericSignature().
                // If it is absent, then no further work is needed and we can return a reference type without generics.
                return Optional.of(new ReferenceTypeImpl(
                        typeSolver.solveType(JavassistUtils.internalNameToCanonicalName(ctClass.getClassFile().getSuperclass())),
                        typeSolver
                ));
            } else {
                // If there is a generic signature present, solve the types and return it.
                SignatureAttribute.ClassSignature classSignature = SignatureAttribute.toClassSignature(ctClass.getGenericSignature());
                return Optional.ofNullable(
                        JavassistUtils.signatureTypeToType(
                                classSignature.getSuperClass(),
                                typeSolver,
                                typeDeclaration
                        ).asReferenceType()
                );
            }
        } catch (BadBytecode e) {
            throw new RuntimeException(e);
        }
    }

    public List<ResolvedReferenceType> getInterfaces() {
        return getInterfaces(false);
    }

    private List<ResolvedReferenceType> getInterfaces(boolean acceptIncompleteList) {
        List<ResolvedReferenceType> interfaces = new ArrayList<>();
        try {
            if (ctClass.getGenericSignature() == null) {
                for (String interfaceType : ctClass.getClassFile().getInterfaces()) {
                    try {
                        ResolvedReferenceTypeDeclaration declaration = typeSolver.solveType(JavassistUtils.internalNameToCanonicalName(interfaceType));
                        interfaces.add(new ReferenceTypeImpl(declaration, typeSolver));
                    } catch (UnsolvedSymbolException e) {
                        if (!acceptIncompleteList) {
                            throw e;
                        }
                    }
                }
            } else {
                SignatureAttribute.ClassSignature classSignature = SignatureAttribute.toClassSignature(ctClass.getGenericSignature());
                for (SignatureAttribute.ClassType interfaceType : classSignature.getInterfaces()) {
                    try {
                        interfaces.add(JavassistUtils.signatureTypeToType(interfaceType, typeSolver, typeDeclaration).asReferenceType());
                    } catch (UnsolvedSymbolException e) {
                        if (!acceptIncompleteList) {
                            throw e;
                        }
                    }
                }
            }
        } catch (BadBytecode e) {
            throw new RuntimeException(e);
        }

        return interfaces;
    }

    public List<ResolvedReferenceType> getAncestors(boolean acceptIncompleteList) {
        List<ResolvedReferenceType> ancestors = new ArrayList<>();

        try {
            getSuperClass().ifPresent(superClass -> ancestors.add(superClass));
        } catch (UnsolvedSymbolException e) {
            if (!acceptIncompleteList) {
                throw e;
            }
        }
        ancestors.addAll(getInterfaces(acceptIncompleteList));
        return ancestors;
    }

    public Set<ResolvedMethodDeclaration> getDeclaredMethods() {
        return Arrays.stream(ctClass.getDeclaredMethods())
                .filter(m -> ((m.getMethodInfo().getAccessFlags() & AccessFlag.BRIDGE) == 0)
                        && ((m.getMethodInfo().getAccessFlags() & AccessFlag.SYNTHETIC) == 0))
                .map(m -> new JavassistMethodDeclaration(m, typeSolver)).collect(Collectors.toSet());
    }

    public List<ResolvedConstructorDeclaration> getConstructors() {
        return Arrays.stream(ctClass.getConstructors())
                .filter(m -> (m.getMethodInfo().getAccessFlags() & AccessFlag.SYNTHETIC) == 0)
                .map(m -> new JavassistConstructorDeclaration(m, typeSolver)).collect(Collectors.toList());
    }

    public List<ResolvedFieldDeclaration> getDeclaredFields() {
        List<ResolvedFieldDeclaration> fields = new ArrayList<>();

        // First consider fields declared on this class
        for (CtField field : ctClass.getDeclaredFields()) {
            fields.add(new JavassistFieldDeclaration(field, typeSolver));
        }

        // Then consider fields inherited from ancestors
        for (ResolvedReferenceType ancestor : typeDeclaration.getAllAncestors()) {
            ancestor.getTypeDeclaration().ifPresent(ancestorTypeDeclaration -> {
                fields.addAll(ancestorTypeDeclaration.getAllFields());
            });
        }

        return fields;
    }

    public List<ResolvedTypeParameterDeclaration> getTypeParameters() {
        if (null == ctClass.getGenericSignature()) {
            return Collections.emptyList();
        } else {
            try {
                SignatureAttribute.ClassSignature classSignature =
                        SignatureAttribute.toClassSignature(ctClass.getGenericSignature());
                return Arrays.<SignatureAttribute.TypeParameter>stream(classSignature.getParameters())
                        .map((tp) -> new JavassistTypeParameter(tp, JavassistFactory.toTypeDeclaration(ctClass, typeSolver), typeSolver))
                        .collect(Collectors.toList());
            } catch (BadBytecode badBytecode) {
                throw new RuntimeException(badBytecode);
            }
        }
    }

    public Optional<ResolvedReferenceTypeDeclaration> containerType() {
        try {
            return ctClass.getDeclaringClass() == null ?
                    Optional.empty() :
                    Optional.of(JavassistFactory.toTypeDeclaration(ctClass.getDeclaringClass(), typeSolver));
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }
    }

    public boolean isAssignableBy(ResolvedType other) {

        if (other.isNull()) {
            return true;
        }

        if (other instanceof LambdaArgumentTypePlaceholder) {
            return typeDeclaration.isFunctionalInterface();
        }

        return other.isAssignableBy(new ReferenceTypeImpl(typeDeclaration, typeSolver));
    }

    public boolean isAssignableBy(ResolvedReferenceTypeDeclaration other) {
        return isAssignableBy(new ReferenceTypeImpl(other, typeSolver));
    }

    /**
     * Get the nested classes.
     * <br>
     * {@code class Foo { class Bar {} }
     * In the example above we expect the nested types for {@code Foo} to be {@code Bar}.
     *
     * @return The nested classes.
     */
    public Set<ResolvedReferenceTypeDeclaration> internalTypes() {
        try {
            return Stream.of(ctClass.getNestedClasses())
                    .map(clazz -> JavassistFactory.toTypeDeclaration(clazz, typeSolver))
                    .collect(Collectors.toSet());
        } catch (NotFoundException e) {
            // This should never happen, since the nested type is defined in the current class
            throw new UnsupportedOperationException("Please report this issue at https://github.com/javaparser/javaparser/issues/new/choose", e);
        }
    }

}
