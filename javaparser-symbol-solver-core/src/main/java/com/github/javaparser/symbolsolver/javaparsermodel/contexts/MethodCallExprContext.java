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

package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.types.*;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.resolution.Value;
import com.github.javaparser.symbolsolver.model.typesystem.*;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import com.github.javaparser.symbolsolver.resolution.MethodResolutionLogic;
import com.github.javaparser.utils.Pair;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

public class MethodCallExprContext extends AbstractJavaParserContext<MethodCallExpr> {

    ///
    /// Constructors
    ///

    public MethodCallExprContext(MethodCallExpr wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    ///
    /// Public methods
    ///

    @Override
    public Optional<ResolvedType> solveGenericType(String name, TypeSolver typeSolver) {
        if(wrappedNode.getScope().isPresent()){
            ResolvedType typeOfScope = JavaParserFacade.get(typeSolver).getType(wrappedNode.getScope().get());
            Optional<ResolvedType> res = typeOfScope.asReferenceType().getGenericParameterByName(name);
            return res;
        } else{
            return Optional.empty();
        }
    }

    @Override
    public String toString() {
        return "MethodCallExprContext{wrapped=" + wrappedNode + "}";
    }

    @Override
    public Optional<MethodUsage> solveMethodAsUsage(String name, List<ResolvedType> argumentsTypes, TypeSolver typeSolver) {
        if (wrappedNode.getScope().isPresent()) {
            Expression scope = wrappedNode.getScope().get();
            // Consider static method calls
            if (scope instanceof NameExpr) {
                String className = ((NameExpr) scope).getName().getId();
                SymbolReference<ResolvedTypeDeclaration> ref = solveType(className, typeSolver);
                if (ref.isSolved()) {
                    SymbolReference<ResolvedMethodDeclaration> m = MethodResolutionLogic.solveMethodInType(ref.getCorrespondingDeclaration(), name, argumentsTypes, typeSolver);
                    if (m.isSolved()) {
                        MethodUsage methodUsage = new MethodUsage(m.getCorrespondingDeclaration());
                        methodUsage = resolveMethodTypeParametersFromExplicitList(typeSolver, methodUsage);
                        methodUsage = resolveMethodTypeParameters(methodUsage, argumentsTypes);
                        return Optional.of(methodUsage);
                    } else {
                        throw new UnsolvedSymbolException(ref.getCorrespondingDeclaration().toString(),
                                "Method '" + name + "' with parameterTypes " + argumentsTypes);
                    }
                }
            }

            ResolvedType typeOfScope = JavaParserFacade.get(typeSolver).getType(scope);
            // we can replace the parameter types from the scope into the typeParametersValues

            Map<ResolvedTypeParameterDeclaration, ResolvedType> inferredTypes = new HashMap<>();
            for (int i = 0; i < argumentsTypes.size(); i++) {
                // by replacing types I can also find new equivalences
                // for example if I replace T=U with String because I know that T=String I can derive that also U equal String
                ResolvedType originalArgumentType = argumentsTypes.get(i);
                ResolvedType updatedArgumentType = usingParameterTypesFromScope(typeOfScope, originalArgumentType, inferredTypes);
                argumentsTypes.set(i, updatedArgumentType);
            }
            for (int i = 0; i < argumentsTypes.size(); i++) {
                ResolvedType updatedArgumentType = applyInferredTypes(argumentsTypes.get(i), inferredTypes);
                argumentsTypes.set(i, updatedArgumentType);
            }

            return solveMethodAsUsage(typeOfScope, name, argumentsTypes, typeSolver, this);
        } else {
            Context parentContext = getParent();
            while (parentContext instanceof MethodCallExprContext) {
                parentContext = parentContext.getParent();
            }
            return parentContext.solveMethodAsUsage(name, argumentsTypes, typeSolver);
        }
    }

    private MethodUsage resolveMethodTypeParametersFromExplicitList(TypeSolver typeSolver, MethodUsage methodUsage) {
        if (wrappedNode.getTypeArguments().isPresent()) {
            final List<ResolvedType> typeArguments = new ArrayList<>();
            for (com.github.javaparser.ast.type.Type ty : wrappedNode.getTypeArguments().get()) {
                typeArguments.add(JavaParserFacade.get(typeSolver).convertToUsage(ty));
            }

            List<ResolvedTypeParameterDeclaration> tyParamDecls = methodUsage.getDeclaration().getTypeParameters();
            if (tyParamDecls.size() == typeArguments.size()) {
                for (int i = 0; i < tyParamDecls.size(); i++) {
                    methodUsage = methodUsage.replaceTypeParameter(tyParamDecls.get(i), typeArguments.get(i));
                }
            }
        }

        return methodUsage;
    }

    @Override
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        return getParent().solveSymbol(name, typeSolver);
    }

    @Override
    public Optional<Value> solveSymbolAsValue(String name, TypeSolver typeSolver) {
        Context parentContext = getParent();
        return parentContext.solveSymbolAsValue(name, typeSolver);
    }

    @Override
    public SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> argumentsTypes, boolean staticOnly, TypeSolver typeSolver) {
        Collection<ResolvedReferenceTypeDeclaration> rrtds = findTypeDeclarations(wrappedNode.getScope(), typeSolver);
        for (ResolvedReferenceTypeDeclaration rrtd : rrtds) {
            SymbolReference<ResolvedMethodDeclaration> res = MethodResolutionLogic.solveMethodInType(rrtd, name, argumentsTypes, false, typeSolver);
            if (res.isSolved()) {
                return res;
            }
        }
        return SymbolReference.unsolved(ResolvedMethodDeclaration.class);
    }

    ///
    /// Private methods
    ///

    private Optional<MethodUsage> solveMethodAsUsage(ResolvedReferenceType refType, String name,
                                                     List<ResolvedType> argumentsTypes, TypeSolver typeSolver,
                                                     Context invokationContext) {
        Optional<MethodUsage> ref = ContextHelper.solveMethodAsUsage(refType.getTypeDeclaration(), name, argumentsTypes, typeSolver, invokationContext, refType.typeParametersValues());
        if (ref.isPresent()) {
            MethodUsage methodUsage = ref.get();

            methodUsage = resolveMethodTypeParametersFromExplicitList(typeSolver, methodUsage);

            // At this stage I should derive from the context and the value some information on the type parameters
            // for example, when calling:
            // myStream.collect(Collectors.toList())
            // I should be able to figure out that considering the type of the stream (e.g., Stream<String>)
            // and considering that Stream has this method:
            //
            // <R,A> R collect(Collector<? super T,A,R> collector)
            //
            // and collector has this method:
            //
            // static <T> Collector<T,?,List<T>>   toList()
            //
            // In this case collect.R has to be equal to List<toList.T>
            // And toList.T has to be equal to ? super Stream.T
            // Therefore R has to be equal to List<? super Stream.T>.
            // In our example Stream.T equal to String, so the R (and the result of the call to collect) is
            // List<? super String>

            Map<ResolvedTypeParameterDeclaration, ResolvedType> derivedValues = new HashMap<>();
            for (int i = 0; i < methodUsage.getParamTypes().size(); i++) {
                ResolvedParameterDeclaration parameter = methodUsage.getDeclaration().getParam(i);
                ResolvedType parameterType = parameter.getType();
                if (parameter.isVariadic()) {
                	parameterType = parameterType.asArrayType().getComponentType();
                }
                inferTypes(argumentsTypes.get(i), parameterType, derivedValues);
            }

            for (Map.Entry<ResolvedTypeParameterDeclaration, ResolvedType> entry : derivedValues.entrySet()){
                methodUsage = methodUsage.replaceTypeParameter(entry.getKey(), entry.getValue());
            }

            ResolvedType returnType = refType.useThisTypeParametersOnTheGivenType(methodUsage.returnType());
            if (returnType != methodUsage.returnType()) {
                methodUsage = methodUsage.replaceReturnType(returnType);
            }
            for (int i = 0; i < methodUsage.getParamTypes().size(); i++) {
                ResolvedType replaced = refType.useThisTypeParametersOnTheGivenType(methodUsage.getParamTypes().get(i));
                methodUsage = methodUsage.replaceParamType(i, replaced);
            }
            return Optional.of(methodUsage);
        } else {
            return ref;
        }
    }

    private void inferTypes(ResolvedType source, ResolvedType target, Map<ResolvedTypeParameterDeclaration, ResolvedType> mappings) {
        if (source.equals(target)) {
            return;
        }
        if (source.isReferenceType() && target.isReferenceType()) {
            ResolvedReferenceType sourceRefType = source.asReferenceType();
            ResolvedReferenceType targetRefType = target.asReferenceType();
            if (sourceRefType.getQualifiedName().equals(targetRefType.getQualifiedName())) {
            	if (!sourceRefType.isRawType() && !targetRefType.isRawType()) {
	                for (int i = 0; i < sourceRefType.typeParametersValues().size(); i++) {
	                    inferTypes(sourceRefType.typeParametersValues().get(i), targetRefType.typeParametersValues().get(i), mappings);
	                }
            	}
            }
            return;
        }
        if (source.isReferenceType() && target.isWildcard()) {
            if (target.asWildcard().isBounded()) {
                inferTypes(source, target.asWildcard().getBoundedType(), mappings);
                return;
            }
            return;
        }
        if (source.isWildcard() && target.isWildcard()) {
            if (source.asWildcard().isBounded() && target.asWildcard().isBounded()){
                inferTypes(source.asWildcard().getBoundedType(), target.asWildcard().getBoundedType(), mappings);
            }
            return;
        }
        if (source.isReferenceType() && target.isTypeVariable()) {
            mappings.put(target.asTypeParameter(), source);
            return;
        }
        if (source.isWildcard() && target.isTypeVariable()) {
            mappings.put(target.asTypeParameter(), source);
            return;
        }
        if (source.isArray() && target.isWildcard()){
            if(target.asWildcard().isBounded()){
                inferTypes(source, target.asWildcard().getBoundedType(), mappings);
                return;
            }
            return;
        }
        if (source.isArray() && target.isTypeVariable()) {
            mappings.put(target.asTypeParameter(), source);
            return;
        }

        if (source.isWildcard() && target.isReferenceType()){
            if (source.asWildcard().isBounded()){
                inferTypes(source.asWildcard().getBoundedType(), target, mappings);
            }
            return;
        }
        if (source.isConstraint() && target.isReferenceType()){
            inferTypes(source.asConstraintType().getBound(), target, mappings);
            return;
        }

        if (source.isConstraint() && target.isTypeVariable()){
            inferTypes(source.asConstraintType().getBound(), target, mappings);
            return;
        }
        if (source.isTypeVariable() && target.isTypeVariable()) {
            mappings.put(target.asTypeParameter(), source);
            return;
        }
        if (source.isPrimitive() || target.isPrimitive()) {
            return;
        }
        if (source.isNull()) {
            return;
        }
        throw new RuntimeException(source.describe() + " " + target.describe());
    }

    private MethodUsage resolveMethodTypeParameters(MethodUsage methodUsage, List<ResolvedType> actualParamTypes) {
        Map<ResolvedTypeParameterDeclaration, ResolvedType> matchedTypeParameters = new HashMap<>();

        if (methodUsage.getDeclaration().hasVariadicParameter()) {
            if (actualParamTypes.size() == methodUsage.getDeclaration().getNumberOfParams()) {
                // the varargs parameter is an Array, so extract the inner type
                ResolvedType expectedType =
                    methodUsage.getDeclaration().getLastParam().getType().asArrayType().getComponentType();
                // the varargs corresponding type can be either T or Array<T>
                ResolvedType actualType =
                    actualParamTypes.get(actualParamTypes.size() - 1).isArray() ?
                        actualParamTypes.get(actualParamTypes.size() - 1).asArrayType().getComponentType() :
                        actualParamTypes.get(actualParamTypes.size() - 1);
                if (!expectedType.isAssignableBy(actualType)) {
                    for (ResolvedTypeParameterDeclaration tp : methodUsage.getDeclaration().getTypeParameters()) {
                        expectedType = MethodResolutionLogic.replaceTypeParam(expectedType, tp, typeSolver);
                    }
                }
                if (!expectedType.isAssignableBy(actualType)) {
                    // ok, then it needs to be wrapped
                    throw new UnsupportedOperationException(
                        String.format("Unable to resolve the type typeParametersValues in a MethodUsage. Expected type: %s, Actual type: %s. Method Declaration: %s. MethodUsage: %s",
                                      expectedType,
                                      actualType,
                                      methodUsage.getDeclaration(),
                                      methodUsage));
                }
                // match only the varargs type
                matchTypeParameters(expectedType, actualType, matchedTypeParameters);
            } else {
                return methodUsage;
            }
        }

        int until = methodUsage.getDeclaration().hasVariadicParameter() ?
            actualParamTypes.size() - 1 :
            actualParamTypes.size();

        for (int i = 0; i < until; i++) {
            ResolvedType expectedType = methodUsage.getParamType(i);
            ResolvedType actualType = actualParamTypes.get(i);
            matchTypeParameters(expectedType, actualType, matchedTypeParameters);
        }
        for (ResolvedTypeParameterDeclaration tp : matchedTypeParameters.keySet()) {
            methodUsage = methodUsage.replaceTypeParameter(tp, matchedTypeParameters.get(tp));
        }
        return methodUsage;
    }

    private void matchTypeParameters(ResolvedType expectedType, ResolvedType actualType, Map<ResolvedTypeParameterDeclaration, ResolvedType> matchedTypeParameters) {
        if (expectedType.isTypeVariable()) {
            if (!actualType.isTypeVariable() && !actualType.isReferenceType()) {
                throw new UnsupportedOperationException(actualType.getClass().getCanonicalName());
            }
            matchedTypeParameters.put(expectedType.asTypeParameter(), actualType);
        } else if (expectedType.isArray()) {
            if (!actualType.isArray()) {
                throw new UnsupportedOperationException(actualType.getClass().getCanonicalName());
            }
            matchTypeParameters(
                    expectedType.asArrayType().getComponentType(),
                    actualType.asArrayType().getComponentType(),
                    matchedTypeParameters);
        } else if (expectedType.isReferenceType()) {
            // avoid cases where the actual type has no type parameters but the expected one has. Such as: "classX extends classY<Integer>"
            if (actualType.isReferenceType() && actualType.asReferenceType().typeParametersValues().size() > 0) {
                int i = 0;
                for (ResolvedType tp : expectedType.asReferenceType().typeParametersValues()) {
                    matchTypeParameters(tp, actualType.asReferenceType().typeParametersValues().get(i), matchedTypeParameters);
                    i++;
                }
            }
        } else if (expectedType.isPrimitive()) {
            // nothing to do
        } else if (expectedType.isWildcard()) {
            // nothing to do
        } else {
            throw new UnsupportedOperationException(expectedType.getClass().getCanonicalName());
        }
    }

    private Optional<MethodUsage> solveMethodAsUsage(ResolvedTypeVariable tp, String name, List<ResolvedType> argumentsTypes, TypeSolver typeSolver, Context invokationContext) {
        for (ResolvedTypeParameterDeclaration.Bound bound : tp.asTypeParameter().getBounds()) {
            Optional<MethodUsage> methodUsage = solveMethodAsUsage(bound.getType(), name, argumentsTypes, typeSolver, invokationContext);
            if (methodUsage.isPresent()) {
                return methodUsage;
            }
        }
        return Optional.empty();
    }

    private Optional<MethodUsage> solveMethodAsUsage(ResolvedType type, String name, List<ResolvedType> argumentsTypes, TypeSolver typeSolver, Context invokationContext) {
        if (type instanceof ResolvedReferenceType) {
            return solveMethodAsUsage((ResolvedReferenceType) type, name, argumentsTypes, typeSolver, invokationContext);
        } else if (type instanceof ResolvedTypeVariable) {
            return solveMethodAsUsage((ResolvedTypeVariable) type, name, argumentsTypes, typeSolver, invokationContext);
        } else if (type instanceof ResolvedWildcard) {
            ResolvedWildcard wildcardUsage = (ResolvedWildcard) type;
            if (wildcardUsage.isSuper()) {
                return solveMethodAsUsage(wildcardUsage.getBoundedType(), name, argumentsTypes, typeSolver, invokationContext);
            } else if (wildcardUsage.isExtends()) {
                throw new UnsupportedOperationException("extends wildcard");
            } else {
                throw new UnsupportedOperationException("unbounded wildcard");
            }
        } else if (type instanceof ResolvedLambdaConstraintType){
            ResolvedLambdaConstraintType constraintType = (ResolvedLambdaConstraintType) type;
            return solveMethodAsUsage(constraintType.getBound(), name, argumentsTypes, typeSolver, invokationContext);
        } else if (type instanceof ResolvedArrayType) {
            // An array inherits methods from Object not from it's component type
            return solveMethodAsUsage(new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver), name, argumentsTypes, typeSolver, invokationContext);
        } else {
            throw new UnsupportedOperationException("type usage: " + type.getClass().getCanonicalName());
        }
    }

    private ResolvedType usingParameterTypesFromScope(ResolvedType scope, ResolvedType type, Map<ResolvedTypeParameterDeclaration, ResolvedType> inferredTypes) {
        if (type.isReferenceType()) {
            for (Pair<ResolvedTypeParameterDeclaration, ResolvedType> entry : type.asReferenceType().getTypeParametersMap()) {
                if (entry.a.declaredOnType() && scope.asReferenceType().getGenericParameterByName(entry.a.getName()).isPresent()) {
                    type = type.replaceTypeVariables(entry.a, scope.asReferenceType().getGenericParameterByName(entry.a.getName()).get(), inferredTypes);
                }
            }
            return type;
        } else {
            return type;
        }
    }

    private ResolvedType applyInferredTypes(ResolvedType type, Map<ResolvedTypeParameterDeclaration, ResolvedType> inferredTypes) {
        for (ResolvedTypeParameterDeclaration tp : inferredTypes.keySet()) {
            type = type.replaceTypeVariables(tp, inferredTypes.get(tp), inferredTypes);
        }
        return type;
    }
}
