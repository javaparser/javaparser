package com.github.javaparser.symbolsolver.resolution.typeinference;

import com.github.javaparser.symbolsolver.model.declarations.TypeParameterDeclaration;
import com.github.javaparser.symbolsolver.model.methods.MethodUsage;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceType;
import com.github.javaparser.symbolsolver.model.typesystem.Type;
import com.github.javaparser.symbolsolver.model.typesystem.TypeVariable;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

/**
 * A MethodType is an ordered 4-tuple consisting of:
 * 1. type parameters: the declarations of any type parameters of the method member.
 * 2. argument types: a list of the types of the arguments to the method member.
 * 3. return type: the return type of the method member.
 * 4. throws clause: exception types declared in the throws clause of the method member.
 *
 * See JLS 8.2
 */
public class MethodType {
    private List<TypeParameterDeclaration> typeParameters;
    private List<Type> formalArgumentTypes;
    private Type returnType;
    private List<Type> exceptionTypes;

    public static MethodType fromMethodUsage(MethodUsage methodUsage) {
        return new MethodType(methodUsage.getDeclaration().getTypeParameters(), methodUsage.getParamTypes(),
                methodUsage.returnType(), methodUsage.exceptionTypes());
    }

    public MethodType(List<TypeParameterDeclaration> typeParameters, List<Type> formalArgumentTypes, Type returnType,
                      List<Type> exceptionTypes) {
        this.typeParameters = typeParameters;
        this.formalArgumentTypes = formalArgumentTypes;
        this.returnType = returnType;
        this.exceptionTypes = exceptionTypes;
    }

    public List<TypeParameterDeclaration> getTypeParameters() {
        return typeParameters;
    }

    public List<Type> getFormalArgumentTypes() {
        return formalArgumentTypes;
    }

    public Type getReturnType() {
        return returnType;
    }

    public List<Type> getExceptionTypes() {
        return exceptionTypes;
    }
}
