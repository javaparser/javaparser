package me.tomassetti.symbolsolver.logic;

import me.tomassetti.symbolsolver.model.declarations.ClassDeclaration;
import me.tomassetti.symbolsolver.model.declarations.InterfaceDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.typesystem.ReferenceTypeUsage;
import me.tomassetti.symbolsolver.resolution.TypeSolver;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

public abstract class AbstractClassDeclaration extends AbstractTypeDeclaration implements ClassDeclaration {

    @Override
    public final List<ReferenceTypeUsage> getAllSuperClasses() {
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
        TypeDeclaration objectType = typeSolver().solveType(Object.class.getCanonicalName());
        ReferenceTypeUsage objectRef = new ReferenceTypeUsage(objectType, typeSolver());
        superclasses.add(objectRef);
        return superclasses.stream().filter((s)->s.getTypeDeclaration().isClass()).collect(Collectors.toList());
    }

    @Override
    public final List<InterfaceDeclaration> getAllInterfaces() {
        // TODO it could specify type parameters: they should appear
        List<InterfaceDeclaration> interfaces = new ArrayList<>();
        //ClassDeclaration superClass = getSuperClass(typeSolver);
        for (InterfaceDeclaration interfaceDeclaration : getInterfaces()){
            interfaces.add(interfaceDeclaration);
            interfaces.addAll(interfaceDeclaration.getAllInterfacesExtended());
        }
        return interfaces;
    }

    protected abstract TypeSolver typeSolver();

}
