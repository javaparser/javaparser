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

import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.UnsolvedSymbolException;
import com.github.javaparser.symbolsolver.model.declarations.MethodDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.TypeDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.TypeParameterDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.ValueDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.resolution.Value;
import com.github.javaparser.symbolsolver.model.methods.MethodUsage;
import com.github.javaparser.symbolsolver.model.typesystem.*;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import com.github.javaparser.symbolsolver.resolution.MethodResolutionLogic;
import javaslang.Tuple2;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

public class MethodCallExprContext extends AbstractJavaParserContext<MethodCallExpr> {

    public MethodCallExprContext(MethodCallExpr wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public Optional<Type> solveGenericType(String name, TypeSolver typeSolver) {
        Type typeOfScope = JavaParserFacade.get(typeSolver).getType(wrappedNode.getScope().get());
        Optional<Type> res = typeOfScope.asReferenceType().getGenericParameterByName(name);
        return res;
    }

    private Optional<MethodUsage> solveMethodAsUsage(ReferenceType refType, String name,
                                                     List<Type> argumentsTypes, TypeSolver typeSolver,
                                                     Context invokationContext) {
        Optional<MethodUsage> ref = ContextHelper.solveMethodAsUsage(refType.getTypeDeclaration(), name, argumentsTypes, typeSolver, invokationContext, refType.typeParametersValues());
        if (ref.isPresent()) {
            MethodUsage methodUsage = ref.get();

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

            Map<TypeParameterDeclaration, Type> derivedValues = new HashMap<>();
            for (int i = 0; i < methodUsage.getParamTypes().size(); i++) {
                //if (this.wrappedNode.getArgs().get(i) instanceof )
                inferTypes(argumentsTypes.get(i), methodUsage.getDeclaration().getParam(i).getType(), derivedValues);
            }

            Type returnType = refType.useThisTypeParametersOnTheGivenType(methodUsage.returnType());
            if (returnType != methodUsage.returnType()) {
                methodUsage = methodUsage.replaceReturnType(returnType);
            }
            for (int i = 0; i < methodUsage.getParamTypes().size(); i++) {
                Type replaced = refType.useThisTypeParametersOnTheGivenType(methodUsage.getParamTypes().get(i));
                methodUsage = methodUsage.replaceParamType(i, replaced);
            }
            return Optional.of(methodUsage);
        } else {
            return ref;
        }
    }

    private void inferTypes(Type source, Type target, Map<TypeParameterDeclaration, Type> mappings) {
        if (source.equals(target)) {
            return;
        }
        if (source.isReferenceType() && target.isReferenceType()) {
            if (source.asReferenceType().getQualifiedName().equals(target.asReferenceType().getQualifiedName())) {
                for (int i=0;i<source.asReferenceType().typeParametersValues().size();i++){
                    inferTypes(source.asReferenceType().typeParametersValues().get(i), target.asReferenceType().typeParametersValues().get(i), mappings);
                }
            }
            return;
        }
        if (source.isReferenceType() && target.isWildcard()){
            if (target.asWildcard().isBounded()) {
                inferTypes(source, target.asWildcard().getBoundedType(), mappings);
                return;
            }
            return;
        }
        if (source.isWildcard() && target.isWildcard()){
            return;
        }
        if (source.isReferenceType() && target.isTypeVariable()){
            mappings.put(target.asTypeParameter(), source);
            return;
        }
        if (source.isWildcard() && target.isTypeVariable()) {
            if (source.asWildcard().isBounded()) {
                inferTypes(source.asWildcard().getBoundedType(), target, mappings);
            }
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

    private MethodUsage resolveMethodTypeParameters(MethodUsage methodUsage, List<Type> actualParamTypes) {
        if (methodUsage.getDeclaration().hasVariadicParameter()) {
            if (actualParamTypes.size() == methodUsage.getDeclaration().getNumberOfParams()) {
                Type expectedType = methodUsage.getDeclaration().getLastParam().getType();
                Type actualType = actualParamTypes.get(actualParamTypes.size() - 1);
                if (!expectedType.isAssignableBy(actualType)) {
                    for (TypeParameterDeclaration tp : methodUsage.getDeclaration().getTypeParameters()) {
                        expectedType = MethodResolutionLogic.replaceTypeParam(expectedType, tp, typeSolver);
                    }
                }
                if (!expectedType.isAssignableBy(actualType)) {
                    // ok, then it needs to be wrapped
                    throw new UnsupportedOperationException(String.format("Unable to resolve the type typeParametersValues in a MethodUsage. Expected type: %s, Actual type: %s. Method Declaration: %s. MethodUsage: %s",
                            expectedType, actualType, methodUsage.getDeclaration(), methodUsage));
                }
            } else {
                // TODO fix
                return methodUsage;
                // ok, then it needs to be wrapped
                //throw new UnsupportedOperationException(String.format("Unable to resolve the type typeParametersValues in a MethodUsage. Actual params: %s, Method Declaration: %s. MethodUsage: %s",
                //        actualParamTypes, methodUsage.getDeclaration(), methodUsage));
            }
        }
        Map<TypeParameterDeclaration, Type> matchedTypeParameters = new HashMap<>();
        for (int i = 0; i < actualParamTypes.size(); i++) {
            Type expectedType = methodUsage.getParamType(i);
            Type actualType = actualParamTypes.get(i);
            matchTypeParameters(expectedType, actualType, matchedTypeParameters);
        }
        for (TypeParameterDeclaration tp : matchedTypeParameters.keySet()) {
            methodUsage = methodUsage.replaceTypeParameter(tp, matchedTypeParameters.get(tp));
        }
        return methodUsage;
    }

    private void matchTypeParameters(Type expectedType, Type actualType, Map<TypeParameterDeclaration, Type> matchedTypeParameters) {
        if (expectedType.isTypeVariable()) {
            if (!expectedType.isTypeVariable()) {
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
            int i = 0;
            for (Type tp : expectedType.asReferenceType().typeParametersValues()) {
                matchTypeParameters(tp, actualType.asReferenceType().typeParametersValues().get(i), matchedTypeParameters);
                i++;
            }
        } else if (expectedType.isPrimitive()) {
            // nothing to do
        } else if (expectedType.isWildcard()) {
            // nothing to do
        } else {
            throw new UnsupportedOperationException(expectedType.getClass().getCanonicalName());
        }
    }

    @Override
    public String toString() {
        return "MethodCallExprContext{wrapped=" + wrappedNode + "}";
    }

    private Optional<MethodUsage> solveMethodAsUsage(TypeVariable tp, String name, List<Type> argumentsTypes, TypeSolver typeSolver, Context invokationContext) {
        for (TypeParameterDeclaration.Bound bound : tp.asTypeParameter().getBounds(typeSolver)) {
            Optional<MethodUsage> methodUsage = solveMethodAsUsage(bound.getType(), name, argumentsTypes, typeSolver, invokationContext);
            if (methodUsage.isPresent()) {
                return methodUsage;
            }
        }
        return Optional.empty();
    }

    private Optional<MethodUsage> solveMethodAsUsage(Type type, String name, List<Type> argumentsTypes, TypeSolver typeSolver, Context invokationContext) {
        if (type instanceof ReferenceType) {
            return solveMethodAsUsage((ReferenceType) type, name, argumentsTypes, typeSolver, invokationContext);
        } else if (type instanceof TypeVariable) {
            return solveMethodAsUsage((TypeVariable) type, name, argumentsTypes, typeSolver, invokationContext);
        } else if (type instanceof Wildcard) {
            Wildcard wildcardUsage = (Wildcard) type;
            if (wildcardUsage.isSuper()) {
                return solveMethodAsUsage(wildcardUsage.getBoundedType(), name, argumentsTypes, typeSolver, invokationContext);
            } else if (wildcardUsage.isExtends()) {
                throw new UnsupportedOperationException("extends wildcard");
            } else {
                throw new UnsupportedOperationException("unbounded wildcard");
            }
        } else if (type instanceof ArrayType) {
            return solveMethodAsUsage(((ArrayType) type).getComponentType(), name, argumentsTypes, typeSolver, invokationContext);
        } else {
            throw new UnsupportedOperationException("type usage: " + type.getClass().getCanonicalName());
        }
    }

    private Type usingParameterTypesFromScope(Type scope, Type type, Map<TypeParameterDeclaration, Type> inferredTypes) {
        if (type.isReferenceType()) {
            for (Tuple2<TypeParameterDeclaration, Type> entry : type.asReferenceType().getTypeParametersMap()) {
                if (entry._1.declaredOnType() && scope.asReferenceType().getGenericParameterByName(entry._1.getName()).isPresent()) {
                    type = type.replaceTypeVariables(entry._1, scope.asReferenceType().getGenericParameterByName(entry._1.getName()).get(), inferredTypes);
                }
            }
            return type;
        } else {
            return type;
        }
    }

    @Override
    public Optional<MethodUsage> solveMethodAsUsage(String name, List<Type> argumentsTypes, TypeSolver typeSolver) {
        // TODO consider call of static methods
        if (wrappedNode.getScope().isPresent()) {

            if (wrappedNode.getScope().get() instanceof NameExpr) {
                String className = ((NameExpr) wrappedNode.getScope().get()).getName();
                SymbolReference<TypeDeclaration> ref = solveType(className, typeSolver);
                if (ref.isSolved()) {
                    SymbolReference<MethodDeclaration> m = MethodResolutionLogic.solveMethodInType(ref.getCorrespondingDeclaration(), name, argumentsTypes, typeSolver);
                    if (m.isSolved()) {
                        MethodUsage methodUsage = new MethodUsage(m.getCorrespondingDeclaration());
                        methodUsage = resolveMethodTypeParameters(methodUsage, argumentsTypes);
                        return Optional.of(methodUsage);
                    } else {
                        throw new UnsolvedSymbolException(ref.getCorrespondingDeclaration().toString(), "Method '" + name + "' with parameterTypes " + argumentsTypes);
                    }
                }
            }

            Type typeOfScope = JavaParserFacade.get(typeSolver).getType(wrappedNode.getScope().get());
            // we can replace the parameter types from the scope into the typeParametersValues

            Map<TypeParameterDeclaration, Type> inferredTypes = new HashMap<>();
            for (int i = 0; i < argumentsTypes.size(); i++) {
                // by replacing types I can also find new equivalences
                // for example if I replace T=U with String because I know that T=String I can derive that also U equal String
                argumentsTypes.set(i, usingParameterTypesFromScope(typeOfScope, argumentsTypes.get(i), inferredTypes));
            }
            for (int i = 0; i < argumentsTypes.size(); i++) {
                argumentsTypes.set(i, applyInferredTypes(argumentsTypes.get(i), inferredTypes));
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

    private Type applyInferredTypes(Type type, Map<TypeParameterDeclaration, Type> inferredTypes) {
        for (TypeParameterDeclaration tp : inferredTypes.keySet()) {
            type = type.replaceTypeVariables(tp, inferredTypes.get(tp), inferredTypes);
        }
        return type;
    }

    @Override
    public SymbolReference<? extends ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        return getParent().solveSymbol(name, typeSolver);
    }

    @Override
    public Optional<Value> solveSymbolAsValue(String name, TypeSolver typeSolver) {
        Context parentContext = getParent();
        return parentContext.solveSymbolAsValue(name, typeSolver);
    }

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<Type> argumentsTypes, TypeSolver typeSolver) {
        if (wrappedNode.getScope().isPresent()) {
            // consider static methods
            if (wrappedNode.getScope().get() instanceof NameExpr) {
                NameExpr scopeAsName = (NameExpr) wrappedNode.getScope().get();
                SymbolReference symbolReference = this.solveType(scopeAsName.getName(), typeSolver);
                if (symbolReference.isSolved() && symbolReference.getCorrespondingDeclaration().isType()) {
                    TypeDeclaration typeDeclaration = symbolReference.getCorrespondingDeclaration().asType();
                    return MethodResolutionLogic.solveMethodInType(typeDeclaration, name, argumentsTypes, typeSolver);
                }
            }

            Type typeOfScope = null;
            try {
                typeOfScope = JavaParserFacade.get(typeSolver).getType(wrappedNode.getScope().get());
            } catch (Exception e) {
                throw new RuntimeException(String.format("Issur calculating the type of the scope of " + this), e);
            }
            if (typeOfScope.isWildcard()) {
                if (typeOfScope.asWildcard().isExtends() || typeOfScope.asWildcard().isSuper()) {
                    return MethodResolutionLogic.solveMethodInType(typeOfScope.asWildcard().getBoundedType().asReferenceType().getTypeDeclaration(), name, argumentsTypes, typeSolver);
                } else {
                    return MethodResolutionLogic.solveMethodInType(new ReflectionClassDeclaration(Object.class, typeSolver), name, argumentsTypes, typeSolver);
                }
            } else if (typeOfScope.isArray() && typeOfScope.asArrayType().getComponentType().isReferenceType()) {
                return MethodResolutionLogic.solveMethodInType(typeOfScope.asArrayType().getComponentType().asReferenceType().getTypeDeclaration(), name, argumentsTypes, typeSolver);
            } else if (typeOfScope.isTypeVariable()) {
                for (TypeParameterDeclaration.Bound bound : typeOfScope.asTypeParameter().getBounds(typeSolver)) {
                    SymbolReference<MethodDeclaration> res = MethodResolutionLogic.solveMethodInType(bound.getType().asReferenceType().getTypeDeclaration(), name, argumentsTypes, typeSolver);
                    if (res.isSolved()) {
                        return res;
                    }
                }
                return SymbolReference.unsolved(MethodDeclaration.class);
            } else {
                return MethodResolutionLogic.solveMethodInType(typeOfScope.asReferenceType().getTypeDeclaration(), name, argumentsTypes, typeSolver);
            }
        } else {
            Type typeOfScope = JavaParserFacade.get(typeSolver).getTypeOfThisIn(wrappedNode);
            return MethodResolutionLogic.solveMethodInType(typeOfScope.asReferenceType().getTypeDeclaration(), name, argumentsTypes, typeSolver);
        }
    }
}
