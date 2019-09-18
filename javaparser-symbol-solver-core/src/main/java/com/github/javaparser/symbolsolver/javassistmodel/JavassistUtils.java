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
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.resolution.MethodResolutionLogic;
import javassist.*;
import javassist.bytecode.*;

import java.util.*;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
class JavassistUtils {

    static Optional<MethodUsage> getMethodUsage(CtClass ctClass, String name, List<ResolvedType> argumentsTypes, TypeSolver typeSolver,
                                                List<ResolvedTypeParameterDeclaration> typeParameters, List<ResolvedType> typeParameterValues) {
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

        try {
            CtClass superClass = ctClass.getSuperclass();
            if (superClass != null) {
                Optional<MethodUsage> ref = JavassistUtils.getMethodUsage(superClass, name, argumentsTypes, typeSolver, typeParameters, typeParameterValues);
                if (ref.isPresent()) {
                    methods.add(ref.get());
                }
            }
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }

        try {
            for (CtClass interfaze : ctClass.getInterfaces()) {
                Optional<MethodUsage> ref = JavassistUtils.getMethodUsage(interfaze, name, argumentsTypes, typeSolver, typeParameters, typeParameterValues);
                if (ref.isPresent()) {
                    methods.add(ref.get());
                }
            }
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }

        return MethodResolutionLogic.findMostApplicableUsage(methods, name, argumentsTypes, typeSolver);
    }

    static ResolvedType signatureTypeToType(SignatureAttribute.Type signatureType, TypeSolver typeSolver, ResolvedTypeParametrizable typeParametrizable) {
        if (signatureType instanceof SignatureAttribute.ClassType) {
            SignatureAttribute.ClassType classType = (SignatureAttribute.ClassType) signatureType;
            List<ResolvedType> typeArguments = classType.getTypeArguments() == null ? Collections.emptyList() : Arrays.stream(classType.getTypeArguments()).map(ta -> typeArgumentToType(ta, typeSolver, typeParametrizable)).collect(Collectors.toList());
            ResolvedReferenceTypeDeclaration typeDeclaration = typeSolver.solveType(
                    removeTypeArguments(internalNameToCanonicalName(getTypeName(classType))));
            return new ReferenceTypeImpl(typeDeclaration, typeArguments, typeSolver);
        } else if (signatureType instanceof SignatureAttribute.TypeVariable) {
            SignatureAttribute.TypeVariable typeVariableSignature = (SignatureAttribute.TypeVariable) signatureType;
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

    private static String getTypeName(SignatureAttribute.ClassType classType) {
        SignatureAttribute.ClassType declaringClass = classType.getDeclaringClass();
        return declaringClass == null ? classType.getName() : getTypeName(declaringClass) + "." + classType.getName();
    }

    private static String removeTypeArguments(String typeName) {
        if (typeName.contains("<")) {
            return typeName.substring(0, typeName.indexOf('<'));
        } else {
            return typeName;
        }
    }

    static String internalNameToCanonicalName(String typeName) {
        return typeName.replaceAll("\\$", ".");
    }

    private static ResolvedType objectTypeArgumentToType(SignatureAttribute.ObjectType typeArgument, TypeSolver typeSolver, ResolvedTypeParametrizable typeParametrizable) {
        if (typeArgument instanceof SignatureAttribute.ClassType) {
            return signatureTypeToType(typeArgument, typeSolver, typeParametrizable);
        } else if (typeArgument instanceof SignatureAttribute.ArrayType) {
            return signatureTypeToType(((SignatureAttribute.ArrayType) typeArgument).getComponentType(), typeSolver, typeParametrizable);
        } else {
            String typeName = typeArgument.jvmTypeName();
            return getGenericParameterByName(typeName, typeParametrizable, typeSolver);
        }
    }

    private static ResolvedType getGenericParameterByName(String typeName, ResolvedTypeParametrizable typeParametrizable, TypeSolver typeSolver) {
        Optional<ResolvedType> type = typeParametrizable.findTypeParameter(typeName).map(ResolvedTypeVariable::new);
        return type.orElseGet(() -> new ReferenceTypeImpl(
                typeSolver.solveType(removeTypeArguments(internalNameToCanonicalName(typeName))),
                typeSolver));
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
                return Optional.ofNullable(attr.variableName(paramNumber + pos));
            }
        }
        return Optional.empty();
    }

}
