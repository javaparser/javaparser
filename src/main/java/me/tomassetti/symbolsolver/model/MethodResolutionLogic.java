package me.tomassetti.symbolsolver.model;

import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;

import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by federico on 02/08/15.
 */
public class MethodResolutionLogic {

    public static boolean isApplicable(MethodDeclaration method, String name, List<TypeUsage> paramTypes) {
        if (!method.getName().equals(name)) {
            return false;
        }
        // TODO Consider varargs
        if (method.getNoParams() != paramTypes.size()) {
            return false;
        }
        for (int i=0; i<method.getNoParams(); i++) {
            if (!method.getParam(i).getType().isAssignableBy(paramTypes.get(i))){
                return false;
            }
        }
        return true;
    }

    public static SymbolReference<MethodDeclaration> findMostApplicable(List<MethodDeclaration> methods, String name, List<TypeUsage> paramTypes){
        List<MethodDeclaration> applicableMethods = methods.stream().filter((m) -> isApplicable(m, name, paramTypes)).collect(Collectors.toList());
        if (applicableMethods.isEmpty()) {
            return SymbolReference.unsolved(MethodDeclaration.class);
        }
        if (applicableMethods.size() == 1) {
            // Find parameters



            return SymbolReference.solved(applicableMethods.get(0));
        } else {
            throw new UnsupportedOperationException();
        }
    }

}
