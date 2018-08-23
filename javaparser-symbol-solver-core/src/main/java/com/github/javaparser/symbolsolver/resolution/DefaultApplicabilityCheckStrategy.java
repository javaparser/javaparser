/**
 * 
 */
package com.github.javaparser.symbolsolver.resolution;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import com.github.javaparser.resolution.ApplicabilityCheckStrategy;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.types.ResolvedArrayType;
import com.github.javaparser.resolution.types.ResolvedType;

/**
 * Strategy for checking if a {@link ResolvedMethodDeclaration} is applicable to the given list of argumentTypes.
 */
public class DefaultApplicabilityCheckStrategy implements ApplicabilityCheckStrategy {

    @Override
    public boolean isApplicable(ResolvedMethodDeclaration method, String name, List<ResolvedType> argumentsTypes,
                                TypeSolver typeSolver, boolean withWildcardTolerance) {
       
        
        if (!method.getName().equals(name)) {
            return false;
        }
        if (method.hasVariadicParameter()) {
            int pos = method.getNumberOfParams() - 1;
            if (method.getNumberOfParams() == argumentsTypes.size()) {
                // check if the last value is directly assignable as an array
                ResolvedType expectedType = method.getLastParam().getType();
                ResolvedType actualType = argumentsTypes.get(pos);
                if (!expectedType.isAssignableBy(actualType)) {
                    for (ResolvedTypeParameterDeclaration tp : method.getTypeParameters()) {
                        expectedType = MethodResolutionLogic.replaceTypeParam(expectedType, tp, typeSolver);
                    }
                    if (!expectedType.isAssignableBy(actualType)) {
                        if (actualType.isArray() && expectedType.isAssignableBy(actualType.asArrayType().getComponentType())) {
                            argumentsTypes.set(pos, actualType.asArrayType().getComponentType());
                        } else {
                            argumentsTypes = MethodResolutionLogic.groupVariadicParamValues(argumentsTypes, pos, method.getLastParam().getType());
                        }
                    }
                } // else it is already assignable, nothing to do
            } else {
                if (pos > argumentsTypes.size()) {
                    return false;
                }
                argumentsTypes = MethodResolutionLogic.groupVariadicParamValues(argumentsTypes, pos, method.getLastParam().getType());
            }
        }

        if (method.getNumberOfParams() != argumentsTypes.size()) {
            return false;
        }
        Map<String, ResolvedType> matchedParameters = new HashMap<>();
        boolean needForWildCardTolerance = false;
        for (int i = 0; i < method.getNumberOfParams(); i++) {
            ResolvedType expectedType = method.getParam(i).getType();
            ResolvedType actualType = argumentsTypes.get(i);
            if ((expectedType.isTypeVariable() && !(expectedType.isWildcard())) && expectedType.asTypeParameter().declaredOnMethod()) {
                matchedParameters.put(expectedType.asTypeParameter().getName(), actualType);
                continue;
            }
            boolean isAssignableWithoutSubstitution = expectedType.isAssignableBy(actualType) ||
                    (method.getParam(i).isVariadic() && new ResolvedArrayType(expectedType).isAssignableBy(actualType));
            if (!isAssignableWithoutSubstitution && expectedType.isReferenceType() && actualType.isReferenceType()) {
                isAssignableWithoutSubstitution = MethodResolutionLogic.isAssignableMatchTypeParameters(
                        expectedType.asReferenceType(),
                        actualType.asReferenceType(),
                        matchedParameters);
            }
            if (!isAssignableWithoutSubstitution) {
                List<ResolvedTypeParameterDeclaration> typeParameters = method.getTypeParameters();
                typeParameters.addAll(method.declaringType().getTypeParameters());
                for (ResolvedTypeParameterDeclaration tp : typeParameters) {
                    expectedType = MethodResolutionLogic.replaceTypeParam(expectedType, tp, typeSolver);
                }

                if (!expectedType.isAssignableBy(actualType)) {
                    if (actualType.isWildcard() && withWildcardTolerance && !expectedType.isPrimitive()) {
                        needForWildCardTolerance = true;
                        continue;
                    }
                    if (method.hasVariadicParameter() && i == method.getNumberOfParams() - 1) {
                        if (new ResolvedArrayType(expectedType).isAssignableBy(actualType)) {
                            continue;
                        }
                    }
                    return false;
                }
            }
        }
        return !withWildcardTolerance || needForWildCardTolerance;
        
        
    }

}
