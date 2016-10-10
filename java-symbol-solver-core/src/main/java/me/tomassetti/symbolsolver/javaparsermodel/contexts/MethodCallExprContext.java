package me.tomassetti.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import me.tomassetti.symbolsolver.resolution.MethodResolutionLogic;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.invokations.MethodUsage;
import me.tomassetti.symbolsolver.model.resolution.*;
import me.tomassetti.symbolsolver.model.typesystem.*;
import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFacade;
import me.tomassetti.symbolsolver.javaparsermodel.UnsolvedSymbolException;
import me.tomassetti.symbolsolver.reflectionmodel.ReflectionClassDeclaration;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

public class MethodCallExprContext extends AbstractJavaParserContext<MethodCallExpr> {

    public MethodCallExprContext(MethodCallExpr wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public Optional<TypeUsage> solveGenericType(String name, TypeSolver typeSolver) {
        if (!wrappedNode.getTypeArgs().isEmpty()) {
            throw new UnsupportedOperationException(name);
        }
        TypeUsage typeOfScope = JavaParserFacade.get(typeSolver).getType(wrappedNode.getScope());
        return typeOfScope.asReferenceTypeUsage().getGenericParameterByName(name);
    }

    private Optional<MethodUsage> solveMethodAsUsage(ReferenceTypeUsage refType, String name,
                                                     List<TypeUsage> parameterTypes, TypeSolver typeSolver,
                                                     Context invokationContext) {
        Optional<MethodUsage> ref = refType.getTypeDeclaration().solveMethodAsUsage(name, parameterTypes, typeSolver, invokationContext, refType.parameters());
        if (ref.isPresent()) {
            MethodUsage methodUsage = ref.get();
            TypeUsage returnType = refType.replaceTypeParams(methodUsage.returnType());
            if (returnType != methodUsage.returnType()) {
                methodUsage = methodUsage.replaceReturnType(returnType);
            }
            for (int i = 0; i < methodUsage.getParamTypes().size(); i++) {
                TypeUsage replaced = refType.replaceTypeParams(methodUsage.getParamTypes().get(i));
                methodUsage = methodUsage.replaceParamType(i, replaced);
            }
            return Optional.of(methodUsage);
        } else {
            return ref;
        }
    }

    private MethodUsage resolveMethodTypeParameters(MethodUsage methodUsage, List<TypeUsage> actualParamTypes) {
        if (methodUsage.getDeclaration().hasVariadicParameter()) {
            if (actualParamTypes.size() == methodUsage.getDeclaration().getNoParams()) {
                TypeUsage expectedType = methodUsage.getDeclaration().getLastParam().getType();
                TypeUsage actualType = actualParamTypes.get(actualParamTypes.size() - 1);
                if (!expectedType.isAssignableBy(actualType)) {
                    for (TypeParameter tp : methodUsage.getDeclaration().getTypeParameters()) {
                        expectedType = MethodResolutionLogic.replaceTypeParam(expectedType, tp, typeSolver);
                    }
                }
                if (!expectedType.isAssignableBy(actualType)) {
                    // ok, then it needs to be wrapped
                    throw new UnsupportedOperationException(String.format("Unable to resolve the type parameters in a MethodUsage. Expected type: %s, Actual type: %s. Method Declaration: %s. MethodUsage: %s",
                            expectedType, actualType, methodUsage.getDeclaration(), methodUsage));
                }
            } else {
                // TODO fix
                return methodUsage;
                // ok, then it needs to be wrapped
                //throw new UnsupportedOperationException(String.format("Unable to resolve the type parameters in a MethodUsage. Actual params: %s, Method Declaration: %s. MethodUsage: %s",
                //        actualParamTypes, methodUsage.getDeclaration(), methodUsage));
            }
        }
        Map<String, TypeUsage> matchedTypeParameters = new HashMap<>();
        for (int i=0;i<actualParamTypes.size();i++) {
            TypeUsage expectedType = methodUsage.getParamType(i, typeSolver);
            TypeUsage actualType = actualParamTypes.get(i);
            matchTypeParameters(expectedType, actualType, matchedTypeParameters);
        }
        for (String tp : matchedTypeParameters.keySet()) {
            methodUsage = methodUsage.replaceNameParam(tp, matchedTypeParameters.get(tp));
        }
        return methodUsage;
    }

    private void matchTypeParameters(TypeUsage expectedType, TypeUsage actualType, Map<String, TypeUsage> matchedTypeParameters) {
        if (expectedType.isTypeVariable()) {
            if (!expectedType.isTypeVariable()) {
                throw new UnsupportedOperationException(actualType.getClass().getCanonicalName());
            }
            matchedTypeParameters.put(expectedType.asTypeParameter().getName(), actualType);
        } else if (expectedType.isArray()) {
            if (!actualType.isArray()) {
                throw new UnsupportedOperationException(actualType.getClass().getCanonicalName());
            }
            matchTypeParameters(
                    expectedType.asArrayTypeUsage().getComponentType(),
                    actualType.asArrayTypeUsage().getComponentType(),
                    matchedTypeParameters);
        } else if (expectedType.isReferenceType()) {
            int i = 0;
            for (TypeUsage tp : expectedType.asReferenceTypeUsage().parameters()) {
                matchTypeParameters(tp, actualType.asReferenceTypeUsage().parameters().get(i), matchedTypeParameters);
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
        return "MethodCallExprContext{wrapped=" + wrappedNode+ "}";
    }

    private Optional<MethodUsage> solveMethodAsUsage(TypeParameterUsage tp, String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver, Context invokationContext) {
        for (TypeParameter.Bound bound : tp.asTypeParameter().getBounds(typeSolver)) {
            Optional<MethodUsage> methodUsage = solveMethodAsUsage(bound.getType(), name, parameterTypes, typeSolver, invokationContext);
            if (methodUsage.isPresent()) {
                return methodUsage;
            }
        }
        return Optional.empty();
    }

    private Optional<MethodUsage> solveMethodAsUsage(TypeUsage typeUsage, String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver, Context invokationContext) {
        if (typeUsage instanceof ReferenceTypeUsage) {
            return solveMethodAsUsage((ReferenceTypeUsage) typeUsage, name, parameterTypes, typeSolver, invokationContext);
        } else if (typeUsage instanceof TypeParameterUsage) {
            return solveMethodAsUsage((TypeParameterUsage) typeUsage, name, parameterTypes, typeSolver, invokationContext);
        } else if (typeUsage instanceof WildcardUsage) {
            WildcardUsage wildcardUsage = (WildcardUsage)typeUsage;
            if (wildcardUsage.isSuper()) {
                return solveMethodAsUsage(wildcardUsage.getBoundedType(), name, parameterTypes, typeSolver, invokationContext);
            } else if (wildcardUsage.isExtends()) {
                throw new UnsupportedOperationException("extends wildcard");
            } else {
                throw new UnsupportedOperationException("unbounded wildcard");
            }
        } else if (typeUsage instanceof ArrayTypeUsage) {
            return solveMethodAsUsage(((ArrayTypeUsage)typeUsage).getComponentType(), name, parameterTypes, typeSolver, invokationContext);
        } else {
            throw new UnsupportedOperationException("type usage: " + typeUsage.getClass().getCanonicalName());
        }
    }

    @Override
    public Optional<MethodUsage> solveMethodAsUsage(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver) {
        // TODO consider call of static methods
        if (wrappedNode.getScope() != null) {
            try {
                TypeUsage typeOfScope = JavaParserFacade.get(typeSolver).getType(wrappedNode.getScope());
                return solveMethodAsUsage(typeOfScope, name, parameterTypes, typeSolver, this);
            } catch (UnsolvedSymbolException e) {
                // ok, maybe it was instead a static access, so let's look for a type
                if (wrappedNode.getScope() instanceof NameExpr) {
                    String className = ((NameExpr) wrappedNode.getScope()).getName();
                    SymbolReference<TypeDeclaration> ref = solveType(className, typeSolver);
                    if (ref.isSolved()) {
                        SymbolReference<MethodDeclaration> m = ref.getCorrespondingDeclaration().solveMethod(name, parameterTypes);
                        if (m.isSolved()) {
                            MethodUsage methodUsage = new MethodUsage(m.getCorrespondingDeclaration(), typeSolver);
                            methodUsage = resolveMethodTypeParameters(methodUsage, parameterTypes);
                            return Optional.of(methodUsage);
                        } else {
                            throw new UnsolvedSymbolException(ref.getCorrespondingDeclaration().toString(), "Method '" + name + "' with parameterTypes " + parameterTypes);
                        }
                    } else {
                        throw e;
                    }
                } else {
                    throw e;
                }
            }
        } else {
            Context parentContext = getParent();
            while (parentContext instanceof MethodCallExprContext) {
                parentContext = parentContext.getParent();
            }
            return parentContext.solveMethodAsUsage(name, parameterTypes, typeSolver);
        }
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
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver) {
        if (wrappedNode.getScope() != null) {
            // consider static methods
            if (wrappedNode.getScope() instanceof NameExpr) {
                NameExpr scopeAsName = (NameExpr)wrappedNode.getScope();
                SymbolReference symbolReference = this.solveType(scopeAsName.getName(), typeSolver);
                if (symbolReference.isSolved() && symbolReference.getCorrespondingDeclaration().isType()) {
                    TypeDeclaration typeDeclaration = symbolReference.getCorrespondingDeclaration().asType();
                    return typeDeclaration.solveMethod(name, parameterTypes);
                }
            }

            TypeUsage typeOfScope = JavaParserFacade.get(typeSolver).getType(wrappedNode.getScope());
            if (typeOfScope.isWildcard()) {
                if (typeOfScope.asWildcard().isExtends() || typeOfScope.asWildcard().isSuper()) {
                    return typeOfScope.asWildcard().getBoundedType().asReferenceTypeUsage().solveMethod(name, parameterTypes);
                } else {
                    return new ReferenceTypeUsageImpl(new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver).solveMethod(name, parameterTypes);
                }
            } else if (typeOfScope.isArray() && typeOfScope.asArrayTypeUsage().getComponentType().isReferenceType()) {
                return typeOfScope.asArrayTypeUsage().getComponentType().asReferenceTypeUsage().solveMethod(name, parameterTypes);
            } else if (typeOfScope.isTypeVariable()) {
                for (TypeParameter.Bound bound : typeOfScope.asTypeParameter().getBounds(typeSolver)) {
                    SymbolReference<MethodDeclaration> res = bound.getType().asReferenceTypeUsage().solveMethod(name, parameterTypes);
                    if (res.isSolved()) {
                        return res;
                    }
                }
                return SymbolReference.unsolved(MethodDeclaration.class);
            } else {
                return typeOfScope.asReferenceTypeUsage().solveMethod(name, parameterTypes);
            }
        } else {
            TypeUsage typeOfScope = JavaParserFacade.get(typeSolver).getTypeOfThisIn(wrappedNode);
            return typeOfScope.asReferenceTypeUsage().solveMethod(name, parameterTypes);
        }
    }
}
