package me.tomassetti.symbolsolver.model.declarations;

import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.usages.TypeUsageOfTypeDeclaration;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * A class declaration.
 */
public interface ClassDeclaration extends TypeDeclaration, TypeParametrized {

    @Override
    default boolean isClass() {
        return true;
    }

    ClassDeclaration getSuperClass(TypeSolver typeSolvers);
    List<InterfaceDeclaration> getInterfaces(TypeSolver typeSolver);

    default List<ClassDeclaration> getAllSuperClasses(TypeSolver typeSolver) {
        // TODO it could specify type parameters: they should appear
        List<ClassDeclaration> superclasses = new ArrayList<>();
        ClassDeclaration superClass = getSuperClass(typeSolver);
        if (superClass != null) {
            superclasses.add(superClass);
            superclasses.addAll(superClass.getAllSuperClasses(typeSolver));
        }
        return superclasses;
    }

    default List<InterfaceDeclaration> getAllInterfaces(TypeSolver typeSolver) {
        // TODO it could specify type parameters: they should appear
        List<InterfaceDeclaration> interfaces = new ArrayList<>();
        ClassDeclaration superClass = getSuperClass(typeSolver);
        for (InterfaceDeclaration interfaceDeclaration : getInterfaces(typeSolver)){
            interfaces.add(interfaceDeclaration);
            interfaces.addAll(interfaceDeclaration.getAllInterfacesExtended(typeSolver));
        }
        return interfaces;
    }

    @Override
    default List<TypeUsageOfTypeDeclaration> getAllAncestors(TypeSolver typeSolver) {
        List<TypeUsageOfTypeDeclaration> ancestors = new LinkedList<>();
        if (getSuperClass(typeSolver) != null) {
            ancestors.add(new TypeUsageOfTypeDeclaration(getSuperClass(typeSolver)));
            ancestors.addAll(getSuperClass(typeSolver).getAllAncestors(typeSolver));
        }
        ancestors.addAll(getAllInterfaces(typeSolver).stream().map((i)->new TypeUsageOfTypeDeclaration(i)).collect(Collectors.<TypeUsageOfTypeDeclaration>toList()));
        return ancestors;
    }

}
