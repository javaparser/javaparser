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

package com.github.javaparser.symbolsolver.reflectionmodel;

import com.github.javaparser.ast.Node;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.logic.GenericTypeInferenceLogic;
import com.github.javaparser.symbolsolver.model.declarations.*;
import com.github.javaparser.symbolsolver.model.methods.MethodUsage;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.Type;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.*;
import java.util.stream.Collectors;

public class ReflectionMethodDeclaration implements MethodDeclaration {

    // TODO
    // This class contains a huge portion of code just copied from JavaParserMethodDeclaration

    private Method method;
    private TypeSolver typeSolver;

    public ReflectionMethodDeclaration(Method method, TypeSolver typeSolver) {
        this.method = method;
        if (method.isSynthetic() || method.isBridge()) {
            throw new IllegalArgumentException();
        }
        this.typeSolver = typeSolver;
    }

    @Override
    public String getName() {
        return method.getName();
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
    public String toString() {
        return "ReflectionMethodDeclaration{" +
                "method=" + method +
                '}';
    }

    @Override
    public boolean isType() {
        return false;
    }

    @Override
    public TypeDeclaration declaringType() {
        if (method.getDeclaringClass().isInterface()) {
            return new ReflectionInterfaceDeclaration(method.getDeclaringClass(), typeSolver);
        } else {
            return new ReflectionClassDeclaration(method.getDeclaringClass(), typeSolver);
        }
    }

    @Override
    public Type getReturnType() {
        return ReflectionFactory.typeUsageFor(method.getGenericReturnType(), typeSolver);
    }

    @Override
    public int getNumberOfParams() {
        return method.getParameterTypes().length;
    }

    @Override
    public ParameterDeclaration getParam(int i) {
        boolean variadic = false;
        if (method.isVarArgs()) {
            variadic = i == (method.getParameterCount() - 1);
        }
        return new ReflectionParameterDeclaration(method.getParameterTypes()[i], method.getGenericParameterTypes()[i], typeSolver, variadic);
    }

    public MethodUsage getUsage(Node node) {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<TypeParameterDeclaration> getTypeParameters() {
        return Arrays.stream(method.getTypeParameters()).map((refTp) -> new ReflectionTypeParameter(refTp, false, typeSolver)).collect(Collectors.toList());
    }

    //@Override
    public MethodUsage resolveTypeVariables(Context context, List<Type> parameterTypes) {
        //return new MethodUsage(new ReflectionMethodDeclaration(method, typeSolver), typeSolver);
        Type returnType = replaceTypeParams(new ReflectionMethodDeclaration(method, typeSolver).getReturnType(), typeSolver, context);
        List<Type> params = new ArrayList<>();
        for (int i = 0; i < method.getParameterCount(); i++) {
            Type replaced = replaceTypeParams(new ReflectionMethodDeclaration(method, typeSolver).getParam(i).getType(), typeSolver, context);
            params.add(replaced);
        }

        // We now look at the type parameter for the method which we can derive from the parameter types
        // and then we replace them in the return type
        Map<TypeParameterDeclaration, Type> determinedTypeParameters = new HashMap<>();
        for (int i = 0; i < getNumberOfParams(); i++) {
            Type formalParamType = getParam(i).getType();
            Type actualParamType = parameterTypes.get(i);
            GenericTypeInferenceLogic.determineTypeParameters(determinedTypeParameters, formalParamType, actualParamType, typeSolver);
        }

        for (TypeParameterDeclaration determinedParam : determinedTypeParameters.keySet()) {
            returnType = returnType.replaceTypeVariables(determinedParam, determinedTypeParameters.get(determinedParam));
        }

        return new MethodUsage(new ReflectionMethodDeclaration(method, typeSolver), params, returnType);
    }

    private Optional<Type> typeParamByName(String name, TypeSolver typeSolver, Context context) {
        int i = 0;
        if (this.getTypeParameters() != null) {
            for (TypeParameterDeclaration tp : this.getTypeParameters()) {
                if (tp.getName().equals(name)) {
                    Type type = this.getParam(i).getType();
                    return Optional.of(type);
                }
                i++;
            }
        }
        return Optional.empty();
    }

    private Type replaceTypeParams(Type type, TypeSolver typeSolver, Context context) {
        if (type.isTypeVariable()) {
            TypeParameterDeclaration typeParameter = type.asTypeParameter();
            if (typeParameter.declaredOnType()) {
                Optional<Type> typeParam = typeParamByName(typeParameter.getName(), typeSolver, context);
                if (typeParam.isPresent()) {
                    type = typeParam.get();
                }
            }
        }

        if (type.isReferenceType()) {
            type = type.asReferenceType().transformTypeParameters(tp -> replaceTypeParams(tp, typeSolver, context));
        }

        return type;
    }

    @Override
    public boolean isAbstract() {
        return Modifier.isAbstract(method.getModifiers());
    }

    @Override
    public boolean isDefaultMethod() {
        return method.isDefault();
    }

    @Override
    public AccessLevel accessLevel() {
        return ReflectionFactory.modifiersToAccessLevel(this.method.getModifiers());
    }

}
