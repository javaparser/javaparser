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
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedFieldDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.core.resolution.MethodUsageResolutionCapability;
import com.github.javaparser.symbolsolver.javaparsermodel.LambdaArgumentTypePlaceholder;
import com.github.javaparser.symbolsolver.logic.AbstractClassDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.resolution.MethodResolutionLogic;
import com.github.javaparser.symbolsolver.resolution.SymbolSolver;
import javassist.CtClass;
import javassist.CtField;
import javassist.CtMethod;
import javassist.NotFoundException;
import javassist.bytecode.AccessFlag;
import javassist.bytecode.BadBytecode;
import javassist.bytecode.SignatureAttribute;
import javassist.bytecode.SyntheticAttribute;

import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
public class JavassistClassDeclaration extends AbstractClassDeclaration implements MethodUsageResolutionCapability {

    private CtClass ctClass;
    private TypeSolver typeSolver;
    private JavassistTypeDeclarationAdapter javassistTypeDeclarationAdapter;

    public JavassistClassDeclaration(CtClass ctClass, TypeSolver typeSolver) {
        if (ctClass == null) {
            throw new IllegalArgumentException();
        }
        if (ctClass.isInterface() || ctClass.isAnnotation() || ctClass.isPrimitive() || ctClass.isEnum()) {
            throw new IllegalArgumentException("Trying to instantiate a JavassistClassDeclaration with something which is not a class: " + ctClass.toString());
        }
        this.ctClass = ctClass;
        this.typeSolver = typeSolver;
        this.javassistTypeDeclarationAdapter = new JavassistTypeDeclarationAdapter(ctClass, typeSolver);
    }

    @Override
    protected ResolvedReferenceType object() {
        return new ReferenceTypeImpl(typeSolver.getSolvedJavaLangObject(), typeSolver);
    }

    @Override
    public boolean hasDirectlyAnnotation(String canonicalName) {
        return ctClass.hasAnnotation(canonicalName);
    }

    @Override
    public Set<ResolvedMethodDeclaration> getDeclaredMethods() {
        return javassistTypeDeclarationAdapter.getDeclaredMethods();
    }

    @Override
    public boolean isAssignableBy(ResolvedReferenceTypeDeclaration other) {
        return isAssignableBy(new ReferenceTypeImpl(other, typeSolver));
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        JavassistClassDeclaration that = (JavassistClassDeclaration) o;

        return ctClass.equals(that.ctClass);
    }

    @Override
    public int hashCode() {
        return ctClass.hashCode();
    }

    @Override
    public String getPackageName() {
        return ctClass.getPackageName();
    }

    @Override
    public String getClassName() {
        String className = ctClass.getName().replace('$', '.');
        if (getPackageName() != null) {
            return className.substring(getPackageName().length() + 1);
        }
        return className;
    }

    @Override
    public String getQualifiedName() {
        return ctClass.getName().replace('$', '.');
    }

    @Deprecated
    public Optional<MethodUsage> solveMethodAsUsage(String name, List<ResolvedType> argumentsTypes,
                                                    Context invokationContext, List<ResolvedType> typeParameterValues) {
        return JavassistUtils.getMethodUsage(ctClass, name, argumentsTypes, typeSolver, getTypeParameters(), typeParameterValues);
    }

    @Deprecated
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        for (CtField field : ctClass.getDeclaredFields()) {
            if (field.getName().equals(name)) {
                return SymbolReference.solved(new JavassistFieldDeclaration(field, typeSolver));
            }
        }

        final String superclassFQN = getSuperclassFQN();
        SymbolReference<? extends ResolvedValueDeclaration> ref = solveSymbolForFQN(name, superclassFQN);
        if (ref.isSolved()) {
            return ref;
        }

        String[] interfaceFQNs = getInterfaceFQNs();
        for (String interfaceFQN : interfaceFQNs) {
            SymbolReference<? extends ResolvedValueDeclaration> interfaceRef = solveSymbolForFQN(name, interfaceFQN);
            if (interfaceRef.isSolved()) {
                return interfaceRef;
            }
        }

        return SymbolReference.unsolved(ResolvedValueDeclaration.class);
    }

    private SymbolReference<? extends ResolvedValueDeclaration> solveSymbolForFQN(String symbolName, String fqn) {
        if (fqn == null) {
            return SymbolReference.unsolved(ResolvedValueDeclaration.class);
        }

        ResolvedReferenceTypeDeclaration fqnTypeDeclaration = typeSolver.solveType(fqn);
        return new SymbolSolver(typeSolver).solveSymbolInType(fqnTypeDeclaration, symbolName);
    }

    private String[] getInterfaceFQNs() {
        return ctClass.getClassFile().getInterfaces();
    }

    private String getSuperclassFQN() {
        return ctClass.getClassFile().getSuperclass();
    }

    @Override
    public List<ResolvedReferenceType> getAncestors(boolean acceptIncompleteList) {
        List<ResolvedReferenceType> ancestors = new ArrayList<>();
        try {
            getSuperClass().ifPresent(superClass -> ancestors.add(superClass));
        } catch (UnsolvedSymbolException e) {
            if (!acceptIncompleteList) {
                // we only throw an exception if we require a complete list; otherwise, we attempt to continue gracefully
                throw e;
            }
        }
        try {
            ancestors.addAll(getInterfaces());
        } catch (UnsolvedSymbolException e) {
            if (!acceptIncompleteList) {
                // we only throw an exception if we require a complete list; otherwise, we attempt to continue gracefully
                throw e;
            }
        }
        return ancestors;
    }

    @Override
    @Deprecated
    public SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> argumentsTypes, boolean staticOnly) {
        List<ResolvedMethodDeclaration> candidates = new ArrayList<>();
        Predicate<CtMethod> staticOnlyCheck = m -> !staticOnly || (staticOnly && Modifier.isStatic(m.getModifiers()));
        for (CtMethod method : ctClass.getDeclaredMethods()) {
            boolean isSynthetic = method.getMethodInfo().getAttribute(SyntheticAttribute.tag) != null;
            boolean isNotBridge = (method.getMethodInfo().getAccessFlags() & AccessFlag.BRIDGE) == 0;
            if (method.getName().equals(name) && !isSynthetic && isNotBridge && staticOnlyCheck.test(method)) {
                ResolvedMethodDeclaration candidate = new JavassistMethodDeclaration(method, typeSolver);
                candidates.add(candidate);

                // no need to search for overloaded/inherited methods if the method has no parameters
                if (argumentsTypes.isEmpty() && candidate.getNumberOfParams() == 0) {
                    return SymbolReference.solved(candidate);
                }
            }
        }

        // add the method declaration of the superclass to the candidates, if present
        getSuperClass()
                .flatMap(ResolvedReferenceType::getTypeDeclaration)
                .ifPresent(superclassTypeDeclaration -> {
                    SymbolReference<ResolvedMethodDeclaration> superClassMethodRef = MethodResolutionLogic.solveMethodInType(
                            superclassTypeDeclaration,
                            name,
                            argumentsTypes,
                            staticOnly
                    );
                    if (superClassMethodRef.isSolved()) {
                        candidates.add(superClassMethodRef.getCorrespondingDeclaration());
                    }
                });

        // add the method declaration of the interfaces to the candidates, if present
        for (ResolvedReferenceType interfaceRef : getInterfaces()) {
            if (interfaceRef.getTypeDeclaration().isPresent()) {
                SymbolReference<ResolvedMethodDeclaration> interfaceMethodRef = MethodResolutionLogic.solveMethodInType(
                        interfaceRef.getTypeDeclaration().get(),
                        name,
                        argumentsTypes,
                        staticOnly
                );
                if (interfaceMethodRef.isSolved()) {
                    candidates.add(interfaceMethodRef.getCorrespondingDeclaration());
                }
            } else {
                // Consider IllegalStateException or similar?
            }
        }

        return MethodResolutionLogic.findMostApplicable(candidates, name, argumentsTypes, typeSolver);
    }

    public ResolvedType getUsage(Node node) {
        return new ReferenceTypeImpl(this, typeSolver);
    }

    @Override
    public boolean isAssignableBy(ResolvedType type) {
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
    public List<ResolvedFieldDeclaration> getAllFields() {
        return javassistTypeDeclarationAdapter.getDeclaredFields();
    }

    @Override
    public String getName() {
        String[] nameElements = ctClass.getSimpleName().replace('$', '.').split("\\.");
        return nameElements[nameElements.length - 1];
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
                                this
                        ).asReferenceType()
                );
            }
        } catch (BadBytecode e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public List<ResolvedReferenceType> getInterfaces() {
        try {
            if (ctClass.getGenericSignature() == null) {
                return Arrays.stream(ctClass.getClassFile().getInterfaces())
                        .map(i -> typeSolver.solveType(JavassistUtils.internalNameToCanonicalName(i)))
                        .map(i -> new ReferenceTypeImpl(i, typeSolver))
                        .collect(Collectors.toList());
            } else {
                SignatureAttribute.ClassSignature classSignature = SignatureAttribute.toClassSignature(ctClass.getGenericSignature());
                return Arrays.stream(classSignature.getInterfaces())
                        .map(i -> JavassistUtils.signatureTypeToType(i, typeSolver, this).asReferenceType())
                        .collect(Collectors.toList());
            }
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
    public List<ResolvedTypeParameterDeclaration> getTypeParameters() {
        return javassistTypeDeclarationAdapter.getTypeParameters();
    }

    @Override
    public AccessSpecifier accessSpecifier() {
        return JavassistFactory.modifiersToAccessLevel(ctClass.getModifiers());
    }

    @Override
    public List<ResolvedConstructorDeclaration> getConstructors() {
        return javassistTypeDeclarationAdapter.getConstructors();
    }

    @Override
    public Optional<ResolvedReferenceTypeDeclaration> containerType() {
        return javassistTypeDeclarationAdapter.containerType();
    }

    @Override
    public Set<ResolvedReferenceTypeDeclaration> internalTypes() {
        try {
            /*
            Get all internal types of the current class and get their corresponding ReferenceTypeDeclaration.
            Finally, return them in a Set.
             */
            return Arrays.stream(ctClass.getDeclaredClasses()).map(itype -> JavassistFactory.toTypeDeclaration(itype, typeSolver)).collect(Collectors.toSet());
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public ResolvedReferenceTypeDeclaration getInternalType(String name) {
        /*
        The name of the ReferenceTypeDeclaration could be composed of the internal class and the outer class, e.g. A$B. That's why we search the internal type in the ending part.
        In case the name is composed of the internal type only, i.e. f.getName() returns B, it will also works.
         */
        Optional<ResolvedReferenceTypeDeclaration> type =
                this.internalTypes().stream().filter(f -> f.getName().endsWith(name)).findFirst();
        return type.orElseThrow(() ->
                new UnsolvedSymbolException("Internal type not found: " + name));
    }

    @Override
    public boolean hasInternalType(String name) {
        /*
        The name of the ReferenceTypeDeclaration could be composed of the internal class and the outer class, e.g. A$B. That's why we search the internal type in the ending part.
        In case the name is composed of the internal type only, i.e. f.getName() returns B, it will also works.
         */
        return this.internalTypes().stream().anyMatch(f -> f.getName().endsWith(name));
    }

    @Override
    public Optional<Node> toAst() {
        return Optional.empty();
    }
}
