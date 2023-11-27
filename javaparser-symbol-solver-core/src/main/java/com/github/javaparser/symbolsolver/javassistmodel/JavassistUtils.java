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

import java.util.*;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import com.github.javaparser.resolution.Context;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParametrizable;
import com.github.javaparser.resolution.logic.MethodResolutionLogic;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.*;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.ContextHelper;

import javassist.CtBehavior;
import javassist.CtClass;
import javassist.CtMethod;
import javassist.Modifier;
import javassist.bytecode.*;

/**
 * @author Federico Tomassetti
 */
class JavassistUtils {

    static Optional<MethodUsage> solveMethodAsUsage(String name, List<ResolvedType> argumentsTypes, TypeSolver typeSolver,
                                                    Context invokationContext, List<ResolvedType> typeParameterValues,
                                                    ResolvedReferenceTypeDeclaration scopeType, CtClass ctClass) {
        List<ResolvedTypeParameterDeclaration> typeParameters = scopeType.getTypeParameters();

        List<MethodUsage> methods = new ArrayList<>();
        for (CtMethod method : ctClass.getDeclaredMethods()) {
            if (method.getName().equals(name)
                    && ((method.getMethodInfo().getAccessFlags() & AccessFlag.BRIDGE) == 0)
                    && ((method.getMethodInfo().getAccessFlags() & AccessFlag.SYNTHETIC) == 0)) {
                MethodUsage methodUsage = new MethodUsage(new JavassistMethodDeclaration(method, typeSolver));
                for (int i = 0; i < typeParameters.size() && i < typeParameterValues.size(); i++) {
                    ResolvedTypeParameterDeclaration tpToReplace = typeParameters.get(i);
                    ResolvedType newValue = typeParameterValues.get(i);
                    methodUsage = methodUsage.replaceTypeParameter(tpToReplace, newValue);
                }
                methods.add(methodUsage);

                // no need to search for overloaded/inherited methods if the method has no parameters
                if (argumentsTypes.isEmpty() && methodUsage.getNoParams() == 0) {
                    return Optional.of(methodUsage);
                }
            }
        }

        for (ResolvedReferenceType ancestor : scopeType.getAncestors()) {
            ancestor.getTypeDeclaration()
                .flatMap(superClassTypeDeclaration -> ancestor.getTypeDeclaration())
                .flatMap(interfaceTypeDeclaration -> ContextHelper.solveMethodAsUsage(interfaceTypeDeclaration, name, argumentsTypes, invokationContext, typeParameterValues))
                .ifPresent(methods::add);
        }

        return MethodResolutionLogic.findMostApplicableUsage(methods, name, argumentsTypes, typeSolver);
    }

    static SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> argumentsTypes, boolean staticOnly,
                                                                  TypeSolver typeSolver, ResolvedReferenceTypeDeclaration scopeType, CtClass ctClass) {
        List<ResolvedMethodDeclaration> candidates = new ArrayList<>();
        Predicate<CtMethod> staticOnlyCheck = m -> !staticOnly || java.lang.reflect.Modifier.isStatic(m.getModifiers());
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

        // add the method declaration of the interfaces to the candidates, if present
        for (ResolvedReferenceType ancestorRefType : scopeType.getAncestors()) {
            Optional<ResolvedReferenceTypeDeclaration> ancestorTypeDeclOpt = ancestorRefType.getTypeDeclaration();
            if (ancestorTypeDeclOpt.isPresent()) {
                SymbolReference<ResolvedMethodDeclaration> ancestorMethodRef = MethodResolutionLogic.solveMethodInType(
                        ancestorTypeDeclOpt.get(),
                        name,
                        argumentsTypes,
                        staticOnly
                );
                if (ancestorMethodRef.isSolved()) {
                    candidates.add(ancestorMethodRef.getCorrespondingDeclaration());
                }
            } else {
                // Consider IllegalStateException or similar?
            }
        }

        return MethodResolutionLogic.findMostApplicable(candidates, name, argumentsTypes, typeSolver);
    }

    static ResolvedType signatureTypeToType(SignatureAttribute.Type signatureType, TypeSolver typeSolver, ResolvedTypeParametrizable typeParametrizable) {
        if (signatureType instanceof SignatureAttribute.ClassType) {
            SignatureAttribute.ClassType classType = (SignatureAttribute.ClassType) signatureType;
            List<ResolvedType> typeArguments = classType.getTypeArguments() == null ? Collections.emptyList() : Arrays.stream(classType.getTypeArguments()).map(ta -> typeArgumentToType(ta, typeSolver, typeParametrizable)).collect(Collectors.toList());
            ResolvedReferenceTypeDeclaration typeDeclaration = typeSolver.solveType(
                    removeTypeArguments(internalNameToCanonicalName(getTypeName(classType))));
            return new ReferenceTypeImpl(typeDeclaration, typeArguments);
        }
            if (signatureType instanceof SignatureAttribute.TypeVariable) {
            SignatureAttribute.TypeVariable typeVariableSignature = (SignatureAttribute.TypeVariable) signatureType;
            Optional<ResolvedTypeParameterDeclaration> typeParameterDeclarationOpt = typeParametrizable.findTypeParameter(typeVariableSignature.getName());
            if (!typeParameterDeclarationOpt.isPresent()) {
                throw new UnsolvedSymbolException("Unable to solve TypeVariable " + typeVariableSignature);
            }
            ResolvedTypeParameterDeclaration typeParameterDeclaration = typeParameterDeclarationOpt.get();
            return new ResolvedTypeVariable(typeParameterDeclaration);
        }
            if (signatureType instanceof SignatureAttribute.ArrayType) {
            SignatureAttribute.ArrayType arrayType = (SignatureAttribute.ArrayType) signatureType;
            ResolvedType baseType = signatureTypeToType(arrayType.getComponentType(), typeSolver, typeParametrizable);
            return getArrayType(baseType, arrayType.getDimension());
        }
            if (signatureType instanceof SignatureAttribute.BaseType) {
            SignatureAttribute.BaseType baseType = (SignatureAttribute.BaseType) signatureType;
            if (baseType.toString().equals("void")) {
                return ResolvedVoidType.INSTANCE;
            }
            return ResolvedPrimitiveType.byName(baseType.toString());
        }
        throw new RuntimeException(signatureType.getClass().getCanonicalName());
    }
    /*
     * Manage dimension of an array
     */
    private static ResolvedType getArrayType(ResolvedType resolvedType, int dimension) {
        if (dimension > 0) return getArrayType(new ResolvedArrayType(resolvedType), --dimension);
        return resolvedType;
    }

    private static String getTypeName(SignatureAttribute.ClassType classType) {
        SignatureAttribute.ClassType declaringClass = classType.getDeclaringClass();
        return declaringClass == null ? classType.getName() : getTypeName(declaringClass) + "." + classType.getName();
    }

    private static String removeTypeArguments(String typeName) {
        if (typeName.contains("<")) {
            return typeName.substring(0, typeName.indexOf('<'));
        }
        return typeName;
    }

    static String internalNameToCanonicalName(String typeName) {
        return typeName.replaceAll("\\$", ".");
    }

    private static ResolvedType objectTypeArgumentToType(SignatureAttribute.ObjectType typeArgument, TypeSolver typeSolver, ResolvedTypeParametrizable typeParametrizable) {
        if (typeArgument instanceof SignatureAttribute.ClassType) {
            return signatureTypeToType(typeArgument, typeSolver, typeParametrizable);
        }
            if (typeArgument instanceof SignatureAttribute.ArrayType) {
            return new ResolvedArrayType(signatureTypeToType(((SignatureAttribute.ArrayType) typeArgument).getComponentType(), typeSolver, typeParametrizable));
        }
        String typeName = typeArgument.jvmTypeName();
        return getGenericParameterByName(typeName, typeParametrizable, typeSolver);
    }

    private static ResolvedType getGenericParameterByName(String typeName, ResolvedTypeParametrizable typeParametrizable, TypeSolver typeSolver) {
        Optional<ResolvedType> type = typeParametrizable.findTypeParameter(typeName).map(ResolvedTypeVariable::new);
        return type.orElseGet(() -> new ReferenceTypeImpl(
                typeSolver.solveType(removeTypeArguments(internalNameToCanonicalName(typeName)))));
    }

    private static ResolvedType typeArgumentToType(SignatureAttribute.TypeArgument typeArgument, TypeSolver typeSolver, ResolvedTypeParametrizable typeParametrizable) {
        if (typeArgument.isWildcard()) {
            if (typeArgument.getType() == null) {
                return ResolvedWildcard.UNBOUNDED;
            }
                    if (typeArgument.getKind() == '+') {
                return ResolvedWildcard.extendsBound(objectTypeArgumentToType(typeArgument.getType(), typeSolver, typeParametrizable));
            }
                    if (typeArgument.getKind() == '-') {
                return ResolvedWildcard.superBound(objectTypeArgumentToType(typeArgument.getType(), typeSolver, typeParametrizable));
            }
            throw new UnsupportedOperationException();
        }
        return objectTypeArgumentToType(typeArgument.getType(), typeSolver, typeParametrizable);
    }

    /**
     * Returns the {@code paramNumber}th parameter of a method or constructor, if it is available.
     * <p>
     * The name is not available, if
     * <ul>
     * <li>the method is abstract, i.e. explicitly declared as abstract or it is a non-default interface method</li>
     * <li>methods and constructors from jar files, which have been compiled without debug symbols</li>
     * </ul>
     * <p>
     * The parameters are counted from 0, skipping the implicit {@code this} parameter of non-static methods.
     *
     * @param method the method to look into
     * @param paramNumber the number of the parameter to look for
     * @return the found parameter name or empty, if the name is not available
     */
    static Optional<String> extractParameterName(CtBehavior method, int paramNumber) {
        MethodInfo methodInfo = method.getMethodInfo();
        CodeAttribute codeAttribute = methodInfo.getCodeAttribute();
        if (codeAttribute != null) {
            LocalVariableAttribute attr = (LocalVariableAttribute) codeAttribute.getAttribute(LocalVariableAttribute
                    .tag);
            if (attr != null) {
                int pos = Modifier.isStatic(method.getModifiers()) ? 0 : 1;
                return getVariableName(attr, paramNumber + pos);
            }
        }
        return Optional.empty();
    }

    private static Optional<String> getVariableName(LocalVariableAttribute attr, int pos) {
    	try {
            return Optional.of(attr.variableNameByIndex(pos));
        } catch (ArrayIndexOutOfBoundsException e) {
            return Optional.empty();
        }
    }

}
