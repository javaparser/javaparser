package me.tomassetti.symbolsolver.logic;

import me.tomassetti.symbolsolver.model.invokations.MethodUsage;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;

import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

public class FunctionalInterfaceLogic {

    public static Optional<MethodUsage> getFunctionalMethod(TypeUsage type) {
        if (type.isReferenceType() && type.asReferenceTypeUsage().getTypeDeclaration().isInterface()) {
            //We need to find all abstract methods
            Set<MethodUsage> methods = type.asReferenceTypeUsage().getTypeDeclaration().getAllMethods().stream().filter(m -> m.getDeclaration().isAbstract()).collect(Collectors.toSet());
            if (methods.size() == 1) {
                return Optional.of(methods.iterator().next());
            } else {
                return Optional.empty();
            }
        } else {
            return Optional.empty();
        }
    }
}
