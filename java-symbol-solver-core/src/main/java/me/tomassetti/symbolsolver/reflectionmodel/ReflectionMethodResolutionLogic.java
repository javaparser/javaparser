package me.tomassetti.symbolsolver.reflectionmodel;

import me.tomassetti.symbolsolver.model.declarations.TypeParameterDeclaration;
import me.tomassetti.symbolsolver.resolution.MethodResolutionLogic;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeParametrizable;
import me.tomassetti.symbolsolver.model.usages.MethodUsage;
import me.tomassetti.symbolsolver.core.resolution.Context;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.usages.typesystem.ReferenceTypeImpl;
import me.tomassetti.symbolsolver.model.usages.typesystem.TypeParameter;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

class ReflectionMethodResolutionLogic {

    static Optional<MethodUsage> solveMethodAsUsage(String name, List<Type> parameterTypes, TypeSolver typeSolver,
                                                    Context invokationContext, List<Type> typeParameterValues,
                                                    TypeParametrizable typeParametrizable, Class clazz) {
        if (typeParameterValues.size() != typeParametrizable.getTypeParameters().size()) {
            // if it is zero we are going to ignore them
            if (!typeParametrizable.getTypeParameters().isEmpty()) {
                // Parameters not specified, so default to Object
                typeParameterValues = new ArrayList<>();
                for (int i = 0; i < typeParametrizable.getTypeParameters().size(); i++) {
                    typeParameterValues.add(new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver));
                }
            }
        }
        List<MethodUsage> methods = new ArrayList<>();
        for (Method method : clazz.getMethods()) {
            if (method.getName().equals(name) && !method.isBridge() && !method.isSynthetic()) {
                MethodDeclaration methodDeclaration = new ReflectionMethodDeclaration(method, typeSolver);
                MethodUsage methodUsage = new MethodUsage(methodDeclaration);
                int i = 0;
                for (TypeParameterDeclaration tp : typeParametrizable.getTypeParameters()) {
                    methodUsage = methodUsage.replaceTypeParameterByName(tp.getName(), typeParameterValues.get(i));
                    i++;
                }
                for (TypeParameterDeclaration methodTypeParameter : methodDeclaration.getTypeParameters()) {
                    methodUsage = methodUsage.replaceTypeParameterByName(methodTypeParameter.getName(), new TypeParameter(methodTypeParameter));
                }
                methods.add(methodUsage);
            }

        }
        final List<Type> finalTypeParameterValues = typeParameterValues;
        parameterTypes = parameterTypes.stream().map((pt) -> {
            int i = 0;
            for (TypeParameterDeclaration tp : typeParametrizable.getTypeParameters()) {
                pt = pt.replaceParam(tp.getName(), finalTypeParameterValues.get(i));
                i++;
            }
            return pt;
        }).collect(Collectors.toList());
        return MethodResolutionLogic.findMostApplicableUsage(methods, name, parameterTypes, typeSolver);
    }
}
