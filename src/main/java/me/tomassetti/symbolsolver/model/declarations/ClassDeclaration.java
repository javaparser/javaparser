package me.tomassetti.symbolsolver.model.declarations;

import me.tomassetti.symbolsolver.model.typesystem.ReferenceTypeUsage;
import me.tomassetti.symbolsolver.resolution.TypeSolver;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Declaration of a Class (not an interface or an enum).
 */
public interface ClassDeclaration extends TypeDeclaration, TypeParametrized {

    @Override
    default boolean isClass() {
        return true;
    }

    ReferenceTypeUsage getSuperClass(TypeSolver typeSolvers);

    List<InterfaceDeclaration> getInterfaces(TypeSolver typeSolver);

    default List<ReferenceTypeUsage> getAllSuperClasses(TypeSolver typeSolver) {
        // TODO it could specify type parameters: they should appear
        List<ReferenceTypeUsage> superclasses = new ArrayList<>();
        ReferenceTypeUsage superClass = getSuperClass(typeSolver);
        if (superClass != null) {
            superclasses.add(superClass);
            superclasses.addAll(superClass.getAllAncestors());
        }
        for (int i=0;i<superclasses.size();i++){
            if (superclasses.get(i).getQualifiedName().equals(Object.class.getCanonicalName())) {
                superclasses.remove(i);
                i--;
            }
        }
        TypeDeclaration objectType = typeSolver.solveType(Object.class.getCanonicalName());
        ReferenceTypeUsage objectRef = new ReferenceTypeUsage(objectType, typeSolver);
        superclasses.add(objectRef);
        return superclasses.stream().filter((s)->s.getTypeDeclaration().isClass()).collect(Collectors.toList());
    }

    default List<InterfaceDeclaration> getAllInterfaces(TypeSolver typeSolver) {
        // TODO it could specify type parameters: they should appear
        List<InterfaceDeclaration> interfaces = new ArrayList<>();
        //ClassDeclaration superClass = getSuperClass(typeSolver);
        for (InterfaceDeclaration interfaceDeclaration : getInterfaces(typeSolver)){
            interfaces.add(interfaceDeclaration);
            interfaces.addAll(interfaceDeclaration.getAllInterfacesExtended(typeSolver));
        }
        return interfaces;
    }

}
