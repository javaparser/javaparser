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

import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParametrizable;
import com.github.javaparser.resolution.types.*;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.*;
import com.github.javaparser.symbolsolver.resolution.SymbolSolver;
import javassist.CtClass;
import javassist.CtMethod;
import javassist.NotFoundException;
import javassist.bytecode.BadBytecode;
import javassist.bytecode.SignatureAttribute;

import java.util.*;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
class JavassistUtils {

    static Optional<MethodUsage> getMethodUsage(CtClass ctClass, String name, List<ResolvedType> argumentsTypes, TypeSolver typeSolver, Context invokationContext) {
        // TODO avoid bridge and synthetic methods
        for (CtMethod method : ctClass.getDeclaredMethods()) {
            if (method.getName().equals(name)) {
                // TODO check typeParametersValues
                MethodUsage methodUsage = new MethodUsage(new JavassistMethodDeclaration(method, typeSolver));
                if (argumentsTypes.size() < methodUsage.getNoParams()) {
                    // this method cannot be a good candidate (except if variadic ?)
                    continue;
                }
                try {
                    if (method.getGenericSignature() != null) {
                        SignatureAttribute.MethodSignature methodSignature = SignatureAttribute.toMethodSignature(method.getGenericSignature());
                        List<ResolvedType> parametersOfReturnType = parseTypeParameters(methodSignature.getReturnType().toString(), typeSolver, invokationContext);
                        ResolvedType newReturnType = methodUsage.returnType();
                        // consume one parametersOfReturnType at the time
                        if (newReturnType.isReferenceType() && parametersOfReturnType.size() > 0) {
                            newReturnType = newReturnType.asReferenceType().transformTypeParameters(tp -> parametersOfReturnType.remove(0));
                        }
                        methodUsage = methodUsage.replaceReturnType(newReturnType);
                    }
                    return Optional.of(methodUsage);
                } catch (BadBytecode e) {
                    throw new RuntimeException(e);
                }
            }
        }

        try {
            CtClass superClass = ctClass.getSuperclass();
            if (superClass != null) {
                Optional<MethodUsage> ref = new JavassistClassDeclaration(superClass, typeSolver).solveMethodAsUsage(name, argumentsTypes, typeSolver, invokationContext, null);
                if (ref.isPresent()) {
                    return ref;
                }
            }
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }

        try {
            for (CtClass interfaze : ctClass.getInterfaces()) {
                Optional<MethodUsage> ref = new JavassistInterfaceDeclaration(interfaze, typeSolver).solveMethodAsUsage(name, argumentsTypes, typeSolver, invokationContext, null);
                if (ref.isPresent()) {
                    return ref;
                }
            }
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }

        return Optional.empty();
    }

    private static List<ResolvedType> parseTypeParameters(String signature, TypeSolver typeSolver, Context invokationContext) {
        String originalSignature = signature;
        if (signature.contains("<")) {
            signature = signature.substring(signature.indexOf('<') + 1);
            if (!signature.endsWith(">")) {
                throw new IllegalArgumentException();
            }
            signature = signature.substring(0, signature.length() - 1);
            if (signature.contains(",")) {
                throw new UnsupportedOperationException();
            }
            if (signature.startsWith("?")) {
                // TODO: check bounds
                List<ResolvedType> types = new ArrayList<>();
                types.add(ResolvedWildcard.UNBOUNDED);
                return types;
            }
            List<ResolvedType> typeParameters = parseTypeParameters(signature, typeSolver, invokationContext);
            if (signature.contains("<")) {
                signature = signature.substring(0, signature.indexOf('<'));
            }
            if (signature.contains(">")) {
                throw new UnsupportedOperationException();
            }

            ResolvedType type = new SymbolSolver(typeSolver).solveTypeUsage(signature, invokationContext);

            if (type.isReferenceType() && typeParameters.size() > 0) {
                type = type.asReferenceType().transformTypeParameters(tp -> typeParameters.remove(0));
            }
            List<ResolvedType> types = new ArrayList<>();
            types.add(type);
            return types;
        } else {
            return Collections.emptyList();
        }
    }

    static ResolvedType signatureTypeToType(SignatureAttribute.Type signatureType, TypeSolver typeSolver, ResolvedTypeParametrizable typeParametrizable) {
        if (signatureType instanceof SignatureAttribute.ClassType) {
            SignatureAttribute.ClassType classType = (SignatureAttribute.ClassType) signatureType;
            List<ResolvedType> typeArguments = classType.getTypeArguments() == null ? Collections.emptyList() : Arrays.stream(classType.getTypeArguments()).map(ta -> typeArgumentToType(ta, typeSolver, typeParametrizable)).collect(Collectors.toList());
            final String typeName =
                    classType.getDeclaringClass() != null ?
                            classType.getDeclaringClass().getName() + "." + classType.getName() :
                            classType.getName();
            ResolvedReferenceTypeDeclaration typeDeclaration = typeSolver.solveType(
                    removeTypeArguments(internalNameToCanonicalName(typeName)));
            return new ReferenceTypeImpl(typeDeclaration, typeArguments, typeSolver);
        } else if (signatureType instanceof SignatureAttribute.TypeVariable) {
            SignatureAttribute.TypeVariable typeVariableSignature = (SignatureAttribute.TypeVariable)signatureType;
            Optional<ResolvedTypeParameterDeclaration> typeParameterDeclarationOpt = typeParametrizable.findTypeParameter(typeVariableSignature.getName());
            if (!typeParameterDeclarationOpt.isPresent()) {
                throw new UnsolvedSymbolException("Unable to solve TypeVariable " + typeVariableSignature);
            }
            ResolvedTypeParameterDeclaration typeParameterDeclaration = typeParameterDeclarationOpt.get();
            return new ResolvedTypeVariable(typeParameterDeclaration);
        } else if (signatureType instanceof SignatureAttribute.ArrayType) {
            SignatureAttribute.ArrayType arrayType = (SignatureAttribute.ArrayType) signatureType;
            return new ResolvedArrayType(signatureTypeToType(arrayType.getComponentType(), typeSolver, typeParametrizable));
        } else if (signatureType instanceof SignatureAttribute.BaseType) {
            SignatureAttribute.BaseType baseType = (SignatureAttribute.BaseType) signatureType;
            if (baseType.toString().equals("void")) {
                return ResolvedVoidType.INSTANCE;
            } else {
                return ResolvedPrimitiveType.byName(baseType.toString());
            }
        } else {
            throw new RuntimeException(signatureType.getClass().getCanonicalName());
        }
    }
    
    private static String removeTypeArguments(String typeName) {
        if (typeName.contains("<")) {
            return typeName.substring(0, typeName.indexOf('<'));
        } else {
            return typeName;
        }
    }

    private static String internalNameToCanonicalName(String typeName) {
        return typeName.replaceAll("\\$", ".");
    }

    private static ResolvedType objectTypeArgumentToType(SignatureAttribute.ObjectType typeArgument, TypeSolver typeSolver, ResolvedTypeParametrizable typeParametrizable) {
        String typeName = typeArgument.jvmTypeName();
        Optional<ResolvedType> type = getGenericParameterByName(typeName, typeParametrizable);
        return type.orElseGet(() -> new ReferenceTypeImpl(
            typeSolver.solveType(removeTypeArguments(internalNameToCanonicalName(typeName))),
            typeSolver));
    }

    private static Optional<ResolvedType> getGenericParameterByName(String typeName, ResolvedTypeParametrizable typeParametrizable) {
        Optional<ResolvedTypeParameterDeclaration> tp = typeParametrizable.findTypeParameter(typeName);
        return tp.map(ResolvedTypeVariable::new);
    }

    private static ResolvedType typeArgumentToType(SignatureAttribute.TypeArgument typeArgument, TypeSolver typeSolver, ResolvedTypeParametrizable typeParametrizable) {
        if (typeArgument.isWildcard()) {
            if (typeArgument.getType() == null) {
                return ResolvedWildcard.UNBOUNDED;
            } else if (typeArgument.getKind() == '+') {
                return ResolvedWildcard.extendsBound(objectTypeArgumentToType(typeArgument.getType(), typeSolver, typeParametrizable));
            } else if (typeArgument.getKind() == '-') {
                return ResolvedWildcard.superBound(objectTypeArgumentToType(typeArgument.getType(), typeSolver, typeParametrizable));
            } else {
                throw new UnsupportedOperationException();
            }
        } else {
            return objectTypeArgumentToType(typeArgument.getType(), typeSolver, typeParametrizable);
        }
    }
}
