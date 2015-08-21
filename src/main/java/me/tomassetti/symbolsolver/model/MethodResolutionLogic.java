package me.tomassetti.symbolsolver.model;

import me.tomassetti.symbolsolver.model.declarations.MethodAmbiguityException;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;

import java.util.List;
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
            if (!method.getParam(i).getType(typeSolver).isAssignableBy(paramTypes.get(i), typeSolver)){
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

}
