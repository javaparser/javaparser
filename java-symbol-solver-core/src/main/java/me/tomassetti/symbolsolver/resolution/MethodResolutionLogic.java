package me.tomassetti.symbolsolver.resolution;

import me.tomassetti.symbolsolver.javaparsermodel.declarations.JavaParserMethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.MethodAmbiguityException;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.invokations.MethodUsage;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.resolution.TypeParameter;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.typesystem.*;

import java.util.*;
import java.util.stream.Collectors;

public class MethodResolutionLogic {

    private static List<TypeUsage> groupVariadicParamValues(List<TypeUsage> paramTypes, int startVariadic, TypeUsage variadicType) {
        List<TypeUsage> res = new ArrayList<>(paramTypes.subList(0, startVariadic));
        List<TypeUsage> variadicValues = paramTypes.subList(startVariadic, paramTypes.size());
        if (variadicValues.isEmpty()) {
            // TODO if there are no variadic values we should default to the bound of the formal type
            res.add(variadicType);
        } else {
            TypeUsage componentType = findCommonType(variadicValues);
            res.add(new ArrayTypeUsage(componentType));
        }
        return res;
    }

    private static TypeUsage findCommonType(List<TypeUsage> variadicValues) {
        if (variadicValues.isEmpty()) {
            throw new IllegalArgumentException();
        }
        // TODO implement this decently
        return variadicValues.get(0);
    }

    public static boolean isApplicable(MethodDeclaration method, String name, List<TypeUsage> paramTypes, TypeSolver typeSolver) {
        List<TypeUsage> originalParamTypes = paramTypes;
        if (!method.getName().equals(name)) {
            return false;
        }
        if (method.hasVariadicParameter()) {
            int pos = method.getNoParams() - 1;
            if (method.getNoParams() == paramTypes.size()) {
                // check if the last value is directly assignable as an array
                TypeUsage expectedType = method.getLastParam().getType();
                TypeUsage actualType = paramTypes.get(pos);
                if (!expectedType.isAssignableBy(actualType)) {
                    for (TypeParameter tp : method.getTypeParameters()) {
                        expectedType = replaceTypeParam(expectedType, tp, typeSolver);
                    }
                    if (!expectedType.isAssignableBy(actualType)) {
                        paramTypes = groupVariadicParamValues(paramTypes, pos, method.getLastParam().getType());
                    }
                } // else it is already assignable, nothing to do
            } else {
                paramTypes = groupVariadicParamValues(paramTypes, pos, method.getLastParam().getType());
            }
        }

        if (method.getNoParams() != paramTypes.size()) {
            return false;
        }
        Map<String, TypeUsage> matchedParameters = new HashMap<>();
        for (int i = 0; i < method.getNoParams(); i++) {
            TypeUsage expectedType = method.getParam(i).getType();
            TypeUsage actualType = paramTypes.get(i);
            boolean isAssignableWithoutSubstitution = expectedType.isAssignableBy(actualType);
            if (!isAssignableWithoutSubstitution && expectedType.isReferenceType() && actualType.isReferenceType()) {
                isAssignableWithoutSubstitution = isAssignableMatchTypeParameters(
                        expectedType.asReferenceTypeUsage(),
                        actualType.asReferenceTypeUsage(),
                        matchedParameters);
            }
            if (!isAssignableWithoutSubstitution) {
                List<TypeParameter> typeParameters = method.getTypeParameters();
                typeParameters.addAll(method.declaringType().getTypeParameters());
                for (TypeParameter tp : typeParameters) {
                    expectedType = replaceTypeParam(expectedType, tp, typeSolver);
                }

                if (!expectedType.isAssignableBy(actualType)) {
                    return false;
                }
            }
        }
        return true;
    }

    public static boolean isAssignableMatchTypeParameters(ReferenceTypeUsage expected, ReferenceTypeUsage actual,
                                                          Map<String, TypeUsage> matchedParameters) {
        if (actual.getQualifiedName().equals(expected.getQualifiedName())) {
            return isAssignableMatchTypeParametersMatchingQName(expected, actual, matchedParameters);
        } else {
            List<ReferenceTypeUsage> ancestors = actual.getAllAncestors();
            for (ReferenceTypeUsage ancestor : ancestors) {
                if (isAssignableMatchTypeParametersMatchingQName(expected, ancestor, matchedParameters)) {
                    return true;
                }
            }
        }
        return false;
    }

    private static boolean isAssignableMatchTypeParametersMatchingQName(ReferenceTypeUsage expected, ReferenceTypeUsage actual,
                                                                        Map<String, TypeUsage> matchedParameters) {

        if (!expected.getQualifiedName().equals(actual.getQualifiedName())) {
            return false;
        }
        if (expected.parameters().size() != actual.parameters().size()) {
            throw new UnsupportedOperationException();
            //return true;
        }
        for (int i = 0; i < expected.parameters().size(); i++) {
            TypeUsage expectedParam = expected.parameters().get(i);
            TypeUsage actualParam = actual.parameters().get(i);
            if (expectedParam.isTypeVariable()) {
                String expectedParamName = expectedParam.asTypeParameter().getName();
                if (!actualParam.isTypeVariable() || !actualParam.asTypeParameter().getName().equals(expectedParamName)) {
                    if (matchedParameters.containsKey(expectedParamName)) {
                        TypeUsage matchedParameter = matchedParameters.get(expectedParamName);
                        if (matchedParameter.isAssignableBy(actualParam)) {
                            return true;
                        } else if (actualParam.isAssignableBy(matchedParameter)) {
                            matchedParameters.put(expectedParamName, actualParam);
                            return true;
                        }
                        return false;
                    } else {
                        matchedParameters.put(expectedParamName, actualParam);
                    }
                }
            } else if (expectedParam.isReferenceType()) {
                if (!expectedParam.equals(actualParam)) {
                    return false;
                }
            } else if (expectedParam.isWildcard()) {
                // TODO verify bounds
                return true;
            } else {
                throw new UnsupportedOperationException(expectedParam.describe());
            }
        }
        return true;
    }

    public static TypeUsage replaceTypeParam(TypeUsage typeUsage, TypeParameter tp, TypeSolver typeSolver) {
        if (typeUsage.isTypeVariable()) {
            if (typeUsage.describe().equals(tp.getName())) {
                List<TypeParameter.Bound> bounds = tp.getBounds(typeSolver);
                if (bounds.size() > 1) {
                    throw new UnsupportedOperationException();
                } else if (bounds.size() == 1) {
                    return bounds.get(0).getType();
                } else {
                    return new ReferenceTypeUsageImpl(typeSolver.solveType(Object.class.getCanonicalName()), typeSolver);
                }
            }
            return typeUsage;
        } else if (typeUsage.isPrimitive()) {
            return typeUsage;
        } else if (typeUsage.isArray()) {
            return new ArrayTypeUsage(replaceTypeParam(typeUsage.asArrayTypeUsage().getComponentType(), tp, typeSolver));
        } else if (typeUsage.isReferenceType()) {
            ReferenceTypeUsage result = typeUsage.asReferenceTypeUsage();
            int i =0;
            for (TypeUsage typeParam : result.parameters()) {
                result = result.replaceParam(i, replaceTypeParam(typeParam, tp, typeSolver)).asReferenceTypeUsage();
                i++;
            }
            return result;
        } else {
            throw new UnsupportedOperationException(typeUsage.getClass().getCanonicalName());
        }
    }

    public static boolean isApplicable(MethodUsage method, String name, List<TypeUsage> paramTypes, TypeSolver typeSolver) {
        if (!method.getName().equals(name)) {
            return false;
        }
        // TODO Consider varargs
        if (method.getNoParams() != paramTypes.size()) {
            return false;
        }
        for (int i = 0; i < method.getNoParams(); i++) {
            TypeUsage expectedType = method.getParamType(i, typeSolver);
            TypeUsage expectedTypeWithoutSubstitutions = expectedType;
            TypeUsage actualType = paramTypes.get(i);
            for (TypeParameter tp : method.getDeclaration().getTypeParameters()) {
                if (tp.getBounds(typeSolver).isEmpty()) {
                    //expectedType = expectedType.replaceParam(tp.getName(), new ReferenceTypeUsageImpl(typeSolver.solveType(Object.class.getCanonicalName()), typeSolver));
                    expectedType = expectedType.replaceParam(tp.getName(), WildcardUsage.extendsBound(new ReferenceTypeUsageImpl(typeSolver.solveType(Object.class.getCanonicalName()), typeSolver)));
                } else if (tp.getBounds(typeSolver).size() == 1) {
                    TypeParameter.Bound bound = tp.getBounds(typeSolver).get(0);
                    if (bound.isExtends()) {
                        //expectedType = expectedType.replaceParam(tp.getName(), bound.getType());
                        expectedType = expectedType.replaceParam(tp.getName(), WildcardUsage.extendsBound(bound.getType()));
                    } else {
                        //expectedType = expectedType.replaceParam(tp.getName(), new ReferenceTypeUsageImpl(typeSolver.solveType(Object.class.getCanonicalName()), typeSolver));
                        expectedType = expectedType.replaceParam(tp.getName(), WildcardUsage.superBound(bound.getType()));
                    }
                } else {
                    throw new UnsupportedOperationException();
                }
            }
            TypeUsage expectedType2 = expectedTypeWithoutSubstitutions;
            for (TypeParameter tp : method.getDeclaration().getTypeParameters()) {
                if (tp.getBounds(typeSolver).isEmpty()) {
                    expectedType2 = expectedType2.replaceParam(tp.getName(), new ReferenceTypeUsageImpl(typeSolver.solveType(Object.class.getCanonicalName()), typeSolver));
                } else if (tp.getBounds(typeSolver).size() == 1) {
                    TypeParameter.Bound bound = tp.getBounds(typeSolver).get(0);
                    if (bound.isExtends()) {
                        expectedType2 = expectedType2.replaceParam(tp.getName(), bound.getType());
                    } else {
                        expectedType2 = expectedType2.replaceParam(tp.getName(), new ReferenceTypeUsageImpl(typeSolver.solveType(Object.class.getCanonicalName()), typeSolver));
                    }
                } else {
                    throw new UnsupportedOperationException();
                }
            }
            if (!expectedType.isAssignableBy(actualType)
                    && !expectedType2.isAssignableBy(actualType)
                    && !expectedTypeWithoutSubstitutions.isAssignableBy(actualType)) {
                        return false;
            }
        }
        return true;
    }

    private static List<MethodDeclaration> getMethodsWithoutDuplicates(List<MethodDeclaration> methods) {
        Set<MethodDeclaration> s = new TreeSet<MethodDeclaration>(new Comparator<MethodDeclaration>() {
            @Override
            public int compare(MethodDeclaration m1, MethodDeclaration m2) {
                if (m1 instanceof JavaParserMethodDeclaration && m2 instanceof JavaParserMethodDeclaration &&
                    ((JavaParserMethodDeclaration)m1).getWrappedNode().equals(((JavaParserMethodDeclaration)m2).getWrappedNode())) {
                    return 0;
                } 
                return 1;
            }
        });
        s.addAll(methods);
        List<MethodDeclaration> res = new ArrayList<>();
        res.addAll(s);
        return res;
    }
    
    /**
     * @param methods    we expect the methods to be ordered such that inherited methods are later in the list
     * @param name
     * @param paramTypes
     * @param typeSolver
     * @return
     */
    public static SymbolReference<MethodDeclaration> findMostApplicable(List<MethodDeclaration> methods, String name, List<TypeUsage> paramTypes, TypeSolver typeSolver) {
        List<MethodDeclaration> applicableMethods = getMethodsWithoutDuplicates(methods).stream().filter((m) -> isApplicable(m, name, paramTypes, typeSolver)).collect(Collectors.toList());
        if (applicableMethods.isEmpty()) {
            return SymbolReference.unsolved(MethodDeclaration.class);
        }
        if (applicableMethods.size() == 1) {
            return SymbolReference.solved(applicableMethods.get(0));
        } else {
            MethodDeclaration winningCandidate = applicableMethods.get(0);
            for (int i = 1; i < applicableMethods.size(); i++) {
                MethodDeclaration other = applicableMethods.get(i);
                if (isMoreSpecific(winningCandidate, other, typeSolver)) {
                    // nothing to do
                } else if (isMoreSpecific(other, winningCandidate, typeSolver)) {
                    winningCandidate = other;
                } else {
                    if (winningCandidate.declaringType().getQualifiedName().equals(other.declaringType().getQualifiedName())) {
                        throw new MethodAmbiguityException("Ambiguous method call: cannot find a most applicable method: " + winningCandidate + ", " + other);
                    } else {
                        // we expect the methods to be ordered such that inherited methods are later in the list
                    }
                }
            }
            return SymbolReference.solved(winningCandidate);
        }
    }

    private static boolean isMoreSpecific(MethodDeclaration methodA, MethodDeclaration methodB, TypeSolver typeSolver) {
        boolean oneMoreSpecificFound = false;
        for (int i = 0; i < methodA.getNoParams(); i++) {
            TypeUsage tdA = methodA.getParam(i).getType();
            TypeUsage tdB = methodB.getParam(i).getType();
            // B is more specific
            if (tdB.isAssignableBy(tdA) && !tdA.isAssignableBy(tdB)) {
                oneMoreSpecificFound = true;
            }
            // A is more specific
            if (tdA.isAssignableBy(tdB) && !tdB.isAssignableBy(tdA)) {
                return false;
            }
        }
        return oneMoreSpecificFound;
    }

    private static boolean isMoreSpecific(MethodUsage methodA, MethodUsage methodB, TypeSolver typeSolver) {
        boolean oneMoreSpecificFound = false;
        for (int i = 0; i < methodA.getNoParams(); i++) {
            TypeUsage tdA = methodA.getParamType(i, typeSolver);
            TypeUsage tdB = methodB.getParamType(i, typeSolver);

            boolean aIsAssignableByB = tdA.isAssignableBy(tdB);
            boolean bIsAssignableByA = tdB.isAssignableBy(tdA);

            // B is more specific
            if (bIsAssignableByA && !aIsAssignableByB) {
                oneMoreSpecificFound = true;
            }
            // A is more specific
            if (aIsAssignableByB && !bIsAssignableByA) {
                return false;
            }
        }
        return oneMoreSpecificFound;
    }

    public static Optional<MethodUsage> findMostApplicableUsage(List<MethodUsage> methods, String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver) {
        List<MethodUsage> applicableMethods = methods.stream().filter((m) -> isApplicable(m, name, parameterTypes, typeSolver)).collect(Collectors.toList());
        if (applicableMethods.isEmpty()) {
            return Optional.empty();
        }
        if (applicableMethods.size() == 1) {
            return Optional.of(applicableMethods.get(0));
        } else {
            MethodUsage winningCandidate = applicableMethods.get(0);
            for (int i = 1; i < applicableMethods.size(); i++) {
                MethodUsage other = applicableMethods.get(i);
                if (isMoreSpecific(winningCandidate, other, typeSolver)) {
                    // nothing to do
                } else if (isMoreSpecific(other, winningCandidate, typeSolver)) {
                    winningCandidate = other;
                } else {
                    if (winningCandidate.declaringType().getQualifiedName().equals(other.declaringType().getQualifiedName())) {
                        if (!areOverride(winningCandidate, other)) {
                            throw new MethodAmbiguityException("Ambiguous method call: cannot find a most applicable method: " + winningCandidate + ", " + other + ". First declared in " + winningCandidate.declaringType().getQualifiedName());
                        }
                    } else {
                        // we expect the methods to be ordered such that inherited methods are later in the list
                        //throw new UnsupportedOperationException();
                    }
                }
            }
            return Optional.of(winningCandidate);
        }
    }

    private static boolean areOverride(MethodUsage winningCandidate, MethodUsage other) {
        if (!winningCandidate.getName().equals(other.getName())) {
            return false;
        }
        if (winningCandidate.getNoParams() != other.getNoParams()) {
            return false;
        }
        for (int i = 0; i < winningCandidate.getNoParams(); i++) {
            if (!winningCandidate.getParamTypes().get(i).equals(other.getParamTypes().get(i))) {
                return false;
            }
        }
        return true;
    }
}
