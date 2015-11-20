package me.tomassetti.symbolsolver.reflectionmodel;

import me.tomassetti.symbolsolver.resolution.MethodResolutionLogic;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeParametrized;
import me.tomassetti.symbolsolver.model.invokations.MethodUsage;
import me.tomassetti.symbolsolver.model.resolution.Context;
import me.tomassetti.symbolsolver.model.resolution.TypeParameter;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.typesystem.ReferenceTypeUsageImpl;
import me.tomassetti.symbolsolver.model.typesystem.TypeParameterUsage;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

class ReflectionMethodResolutionLogic {

    static Optional<MethodUsage> solveMethodAsUsage(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver,
                                                    Context invokationContext, List<TypeUsage> typeParameterValues,
                                                    TypeParametrized typeParametrized, Class clazz) {
        if (typeParameterValues.size() != typeParametrized.getTypeParameters().size()) {
            //if (typeParameterValues.size() != 0){
            //    throw new UnsupportedOperationException("I have solved parameters for " + clazz.getCanonicalName() +". Values given are: "+typeParameterValues);
            //}
            // if it is zero we are going to ignore them
            if (typeParametrized.getTypeParameters().size() != 0) {
                // Parameters not specified, so default to Object
                typeParameterValues = new ArrayList<>();
                for (int i = 0; i < typeParametrized.getTypeParameters().size(); i++) {
                    typeParameterValues.add(new ReferenceTypeUsageImpl(new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver));
                }
            }
        }
        List<MethodUsage> methods = new ArrayList<>();
        for (Method method : clazz.getMethods()) {
            if (method.getName().equals(name) && !method.isBridge() && !method.isSynthetic()) {
                MethodDeclaration methodDeclaration = new ReflectionMethodDeclaration(method, typeSolver);
                MethodUsage methodUsage = new MethodUsage(methodDeclaration, typeSolver);
                int i = 0;
                for (TypeParameter tp : typeParametrized.getTypeParameters()) {
                    methodUsage = methodUsage.replaceNameParam(tp.getName(), typeParameterValues.get(i));
                    i++;
                }
                for (TypeParameter methodTypeParameter : methodDeclaration.getTypeParameters()) {
                    methodUsage = methodUsage.replaceNameParam(methodTypeParameter.getName(), new TypeParameterUsage(methodTypeParameter));
                }
                methods.add(methodUsage);
            }

        }
        final List<TypeUsage> finalTypeParameterValues = typeParameterValues;
        parameterTypes = parameterTypes.stream().map((pt) -> {
            int i = 0;
            for (TypeParameter tp : typeParametrized.getTypeParameters()) {
                pt = pt.replaceParam(tp.getName(), finalTypeParameterValues.get(i));
                i++;
            }
            return pt;
        }).collect(Collectors.toList());
        return MethodResolutionLogic.findMostApplicableUsage(methods, name, parameterTypes, typeSolver);
    }
}
