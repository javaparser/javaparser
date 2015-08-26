package me.tomassetti.symbolsolver.model;

import me.tomassetti.symbolsolver.model.declarations.MethodAmbiguityException;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.reflection.ReflectionClassDeclaration;
import me.tomassetti.symbolsolver.model.usages.MethodUsage;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;
import me.tomassetti.symbolsolver.model.usages.TypeUsageOfTypeDeclaration;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * Created by federico on 02/08/15.
 */
public class MethodResolutionLogic {

    public static boolean isApplicable(MethodDeclaration method, String name, List<TypeUsage> paramTypes, TypeSolver typeSolver) {
        if (!method.getName().equals(name)) {
            return false;
        }
        // TODO Consider varargs
        if (method.getNoParams() != paramTypes.size()) {
            return false;
        }
        for (int i=0; i<method.getNoParams(); i++) {
            TypeUsage expectedType = method.getParam(i).getType(typeSolver);
            boolean isAssignableWithoutSubstitution = expectedType.isAssignableBy(paramTypes.get(i), typeSolver);
            if (!isAssignableWithoutSubstitution) {
                for (TypeParameter tp : method.getTypeParameters()) {
                    expectedType = replaceTypeParam(expectedType, tp, typeSolver);
                }

                if (!expectedType.isAssignableBy(paramTypes.get(i), typeSolver)) {
                    return false;
                }
            }
        }
        return true;
    }

    private static TypeUsage replaceTypeParam(TypeUsage typeUsage, TypeParameter tp, TypeSolver typeSolver){
        if (typeUsage.isTypeVariable()) {
            if (typeUsage.getTypeName().equals(tp.getName())) {
                List<TypeParameter.Bound> bounds = tp.getBounds(typeSolver);
                if (bounds.size() > 1) {
                    throw new UnsupportedOperationException();
                } else if (bounds.size() == 1){
                    return bounds.get(0).getType();
                } else {
                    return new TypeUsageOfTypeDeclaration(new ReflectionClassDeclaration(Object.class));
                }
            }
        }
        // TODO consider annidated types
        return typeUsage;
    }

    public static boolean isApplicable(MethodUsage method, String name, List<TypeUsage> paramTypes, TypeSolver typeSolver) {
        if (!method.getName().equals(name)) {
            return false;
        }
        // TODO Consider varargs
        if (method.getNoParams() != paramTypes.size()) {
            return false;
        }
        for (int i=0; i<method.getNoParams(); i++) {
            if (!method.getParamType(i, typeSolver).isAssignableBy(paramTypes.get(i), typeSolver)){
                return false;
            }
        }
        return true;
    }

    /**
     *
     * @param methods we expect the methods to be ordered such that inherited methods are later in the list
     * @param name
     * @param paramTypes
     * @param typeSolver
     * @return
     */
    public static SymbolReference<MethodDeclaration> findMostApplicable(List<MethodDeclaration> methods, String name, List<TypeUsage> paramTypes, TypeSolver typeSolver){
        List<MethodDeclaration> applicableMethods = methods.stream().filter((m) -> isApplicable(m, name, paramTypes, typeSolver)).collect(Collectors.toList());
        if (applicableMethods.isEmpty()) {
            return SymbolReference.unsolved(MethodDeclaration.class);
        }
        if (applicableMethods.size() == 1) {
            return SymbolReference.solved(applicableMethods.get(0));
        } else {
            MethodDeclaration winningCandidate = applicableMethods.get(0);
            for (int i=1; i<applicableMethods.size(); i++) {
                MethodDeclaration other = applicableMethods.get(i);
                if (isMoreSpecific(winningCandidate, other, typeSolver)) {
                    // nothing to do
                } else if (isMoreSpecific(other, winningCandidate, typeSolver)) {
                    winningCandidate = other;
                } else {
                    if (winningCandidate.declaringType().getQualifiedName().equals(other.declaringType().getQualifiedName())) {
                        throw new MethodAmbiguityException("Ambiguous method call: cannot find a most applicable method: "+winningCandidate+", "+other);
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
        for (int i=0; i < methodA.getNoParams(); i++){
            TypeUsage tdA = methodA.getParam(i).getType(typeSolver);
            TypeUsage tdB = methodB.getParam(i).getType(typeSolver);
            // B is more specific
            if (tdB.isAssignableBy(tdA, typeSolver) && !tdA.isAssignableBy(tdB, typeSolver)) {
                oneMoreSpecificFound = true;
            }
            // A is more specific
            if (tdA.isAssignableBy(tdB, typeSolver) && !tdB.isAssignableBy(tdA, typeSolver)) {
                return false;
            }
        }
        return oneMoreSpecificFound;
    }

    private static boolean isMoreSpecific(MethodUsage methodA, MethodUsage methodB, TypeSolver typeSolver) {
        boolean oneMoreSpecificFound = false;
        for (int i=0; i < methodA.getNoParams(); i++){
            TypeUsage tdA = methodA.getParamType(i, typeSolver);
            TypeUsage tdB = methodB.getParamType(i, typeSolver);

            boolean aIsAssignableByB = tdA.isAssignableBy(tdB, typeSolver);
            boolean bIsAssignableByA = tdB.isAssignableBy(tdA, typeSolver);

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
            for (int i=1; i<applicableMethods.size(); i++) {
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
        for (int i=0;i<winningCandidate.getNoParams();i++) {
            if (!winningCandidate.getParamTypes().get(i).equals(other.getParamTypes().get(i))) {
                return false;
            }
        }
        return true;
    }
}
