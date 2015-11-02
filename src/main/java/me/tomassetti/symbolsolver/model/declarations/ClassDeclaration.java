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

    /**
     * This is a ReferenceTypeUsage because it could contain type parameters.
     * For example: class A extends B<Integer, String>.
     *
     * Note that only the Object class should not have a superclass and therefore
     * return null.
     */
    ReferenceTypeUsage getSuperClass();

    /**
     * Return all the interfaces implemented directly by this class.
     * It does not include the interfaces implemented by superclasses or extended
     * by the interfaces implemented.
     */
    List<InterfaceDeclaration> getInterfaces();

    default List<ReferenceTypeUsage> getAllSuperClasses(TypeSolver typeSolver) {
        // TODO it could specify type parameters: they should appear
        List<ReferenceTypeUsage> superclasses = new ArrayList<>();
        ReferenceTypeUsage superClass = getSuperClass();
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
        for (InterfaceDeclaration interfaceDeclaration : getInterfaces()){
            interfaces.add(interfaceDeclaration);
            interfaces.addAll(interfaceDeclaration.getAllInterfacesExtended(typeSolver));
        }
        return interfaces;
    }

}
