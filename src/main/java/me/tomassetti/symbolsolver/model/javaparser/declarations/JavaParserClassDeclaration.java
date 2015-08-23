package me.tomassetti.symbolsolver.model.javaparser.declarations;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import me.tomassetti.symbolsolver.model.*;
import me.tomassetti.symbolsolver.model.declarations.FieldDeclaration;
import me.tomassetti.symbolsolver.model.declarations.*;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.javaparser.JavaParserFactory;
import me.tomassetti.symbolsolver.model.javaparser.UnsolvedSymbolException;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by federico on 30/07/15.
 */
public class JavaParserClassDeclaration implements ClassDeclaration {

    public JavaParserClassDeclaration(com.github.javaparser.ast.body.ClassOrInterfaceDeclaration wrappedNode) {
        if (wrappedNode.isInterface()) {
            throw new IllegalArgumentException("Interface given");
        }
        this.wrappedNode = wrappedNode;
    }

    private com.github.javaparser.ast.body.ClassOrInterfaceDeclaration wrappedNode;

    @Override
    public Context getContext() {
        return JavaParserFactory.getContext(wrappedNode);
    }

    @Override
    public TypeUsage getUsage(Node node) {
        throw new UnsupportedOperationException();
    }

    @Override
    public String getName() {
        return wrappedNode.getName();
    }

    @Override
    public boolean isField() {
        return false;
    }

    @Override
    public boolean isParameter() {
        return false;
    }

    @Override
    public boolean isVariable() {
        return false;
    }

    @Override
    public boolean isType() {
        return true;
    }

    @Override
    public boolean isClass() {
        return !wrappedNode.isInterface();
    }

    @Override
    public ClassDeclaration getSuperClass(TypeSolver typeSolver) {
        if (wrappedNode.getExtends() == null || wrappedNode.getExtends().isEmpty()) {
            return typeSolver.solveType("java.lang.Object").asType().asClass();
        } else {
            SymbolReference<TypeDeclaration> ref = solveType(wrappedNode.getExtends().get(0).getName(), typeSolver);
            if (!ref.isSolved()) {
                throw new UnsolvedSymbolException(wrappedNode.getExtends().get(0).getName());
            }
            return ref.getCorrespondingDeclaration().asClass();
        }
    }

    @Override
    public List<InterfaceDeclaration> getInterfaces(TypeSolver typeSolver) {
        List<InterfaceDeclaration> interfaces = new ArrayList<>();
        if (wrappedNode.getImplements() != null) {
            for (ClassOrInterfaceType t : wrappedNode.getImplements()) {
                interfaces.add(solveType(t.getName(), typeSolver).getCorrespondingDeclaration().asType().asInterface());
            }
        }
        return interfaces;
    }

    public ClassDeclaration asClass() {
        return this;
    }

    @Override
    public boolean isInterface() {
        return wrappedNode.isInterface();
    }

    @Override
    public String getQualifiedName() {
        String containerName = containerName("", wrappedNode.getParentNode());
        if (containerName.isEmpty()) {
            return wrappedNode.getName();
        } else {
            return containerName + "." + wrappedNode.getName();
        }
    }

    @Override
    public boolean isAssignableBy(TypeDeclaration other, TypeSolver typeSolver) {
        List<TypeDeclaration> ancestorsOfOther = other.getAllAncestors(typeSolver);
        ancestorsOfOther.add(other);
        for (TypeDeclaration ancestorOfOther : ancestorsOfOther) {
            if (ancestorOfOther.getQualifiedName().equals(this.getQualifiedName())) {
                return true;
            }
        }
        return false;
    }

    private String containerName(String base, Node container) {
        if (container instanceof com.github.javaparser.ast.body.ClassOrInterfaceDeclaration) {
            String b = containerName(base, container.getParentNode());
            String cn = ((com.github.javaparser.ast.body.ClassOrInterfaceDeclaration)container).getName();
            if (b.isEmpty()) {
                return cn;
            } else {
                return b + "." + cn;
            }
        } else if (container instanceof CompilationUnit) {
            PackageDeclaration p = ((CompilationUnit) container).getPackage();
            if (p != null) {
                String b = p.getName().toString();
                if (base.isEmpty()) {
                    return b;
                } else {
                    return b + "." + base;
                }
            } else {
                return base;
            }
        } else if (container != null) {
            return containerName(base, container.getParentNode());
        } else {
            return base;
        }
    }

    @Override
    public boolean isAssignableBy(TypeUsage typeUsage, TypeSolver typeSolver) {
        if (typeUsage.isNull()) {
            return true;
        }
        if (typeUsage.isReferenceType()){
            TypeDeclaration other = typeSolver.solveType(typeUsage.getTypeName());
            return isAssignableBy(other, typeSolver);
        } else {
            throw new UnsupportedOperationException();
        }
    }

    @Override
    public boolean canBeAssignedTo(TypeDeclaration other, TypeSolver typeSolver) {
        // TODO consider generic types
        if (this.getQualifiedName().equals(other.getQualifiedName())) {
            return true;
        }
        if (this.wrappedNode.getExtends() != null){
            for (ClassOrInterfaceType type : wrappedNode.getExtends()){
                TypeDeclaration ancestor = new SymbolSolver(typeSolver).solveType(type);
                if (ancestor.canBeAssignedTo(other, typeSolver)) {
                    return true;
                }
            }
        }

        if (this.wrappedNode.getImplements() != null){
            for (ClassOrInterfaceType type : wrappedNode.getImplements()){
                TypeDeclaration ancestor = new SymbolSolver(typeSolver).solveType(type);
                if (ancestor.canBeAssignedTo(other, typeSolver)) {
                    return true;
                }
            }
        }

        return false;
    }

    @Override
    public boolean isTypeVariable() {
        return false;
    }

    @Override
    public FieldDeclaration getField(String name, TypeSolver typeSolver) {
        for (BodyDeclaration member : this.wrappedNode.getMembers()) {
            if (member instanceof com.github.javaparser.ast.body.FieldDeclaration){
                com.github.javaparser.ast.body.FieldDeclaration field = (com.github.javaparser.ast.body.FieldDeclaration)member;
                for (VariableDeclarator vd : field.getVariables()) {
                    if (vd.getId().getName().equals(name)){
                        return new JavaParserFieldDeclaration(vd);
                    }
                }
            }
        }

        throw new UnsupportedOperationException("Derived fields");
    }

    @Override
    public String toString() {
        return "JavaParserClassDeclaration{" +
                "wrappedNode=" + wrappedNode +
                '}';
    }

    @Override
    public boolean hasField(String name, TypeSolver typeSolver) {
        for (BodyDeclaration member : this.wrappedNode.getMembers()) {
            if (member instanceof com.github.javaparser.ast.body.FieldDeclaration){
                com.github.javaparser.ast.body.FieldDeclaration field = (com.github.javaparser.ast.body.FieldDeclaration)member;
                for (VariableDeclarator vd : field.getVariables()) {
                    if (vd.getId().getName().equals(name)){
                        return true;
                    }
                }
            }
        }

        throw new UnsupportedOperationException("Derived fields");
    }

    @Override
    public SymbolReference<? extends ValueDeclaration> solveSymbol(String substring, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }

    @Override
    public SymbolReference<TypeDeclaration> solveType(String name, TypeSolver typeSolver) {
        if (this.wrappedNode.getName().equals(name)){
            return SymbolReference.solved(this);
        }
        if (this.wrappedNode.getTypeParameters() != null) {
            for (com.github.javaparser.ast.TypeParameter typeParameter : this.wrappedNode.getTypeParameters()) {
                if (typeParameter.getName().equals(name)) {
                    return SymbolReference.solved(new JavaParserTypeVariableDeclaration(typeParameter));
                }
            }
        }

        // Internal classes
        for (BodyDeclaration member : this.wrappedNode.getMembers()){
            if (member instanceof com.github.javaparser.ast.body.TypeDeclaration) {
                com.github.javaparser.ast.body.TypeDeclaration internalType = (com.github.javaparser.ast.body.TypeDeclaration) member;
                String prefix = internalType.getName() + ".";
                if (internalType.getName().equals(name)) {
                    if (internalType instanceof ClassOrInterfaceDeclaration) {
                        return SymbolReference.solved(new JavaParserClassDeclaration((com.github.javaparser.ast.body.ClassOrInterfaceDeclaration) internalType));
                    } else if (internalType instanceof EnumDeclaration) {
                        return SymbolReference.solved(new JavaParserEnumDeclaration((com.github.javaparser.ast.body.EnumDeclaration) internalType));
                    } else {
                        throw new UnsupportedOperationException();
                    }
                } else if (name.startsWith(prefix) && name.length() > prefix.length()) {
                    if (internalType instanceof ClassOrInterfaceDeclaration) {
                        return new JavaParserClassDeclaration((com.github.javaparser.ast.body.ClassOrInterfaceDeclaration) internalType).solveType(name.substring(prefix.length()), typeSolver);
                    } else if (internalType instanceof EnumDeclaration) {
                        return new JavaParserEnumDeclaration((com.github.javaparser.ast.body.EnumDeclaration) internalType).solveType(name.substring(prefix.length()), typeSolver);
                    } else {
                        throw new UnsupportedOperationException();
                    }
                }
            }
        }

        String prefix = wrappedNode.getName() + ".";
        if (name.startsWith(prefix) && name.length() > prefix.length()){
            return new JavaParserClassDeclaration(this.wrappedNode).solveType(name.substring(prefix.length()), typeSolver);
        }

        //return SymbolReference.unsolved(TypeDeclaration.class);
        return getContext().getParent().solveType(name, typeSolver);
    }

    @Override
    public List<TypeDeclaration> getAllAncestors(TypeSolver typeSolver) {
        List<TypeDeclaration> ancestors = new ArrayList<>();
        if (wrappedNode.getExtends() != null) {
            for (ClassOrInterfaceType extended : wrappedNode.getExtends()){
                SymbolReference<TypeDeclaration> superclass = solveType(extended.getName(), typeSolver);
                if (!superclass.isSolved()) {
                    throw new UnsolvedSymbolException(extended.getName());
                }
                ancestors.add(superclass.getCorrespondingDeclaration());
                ancestors.addAll(superclass.getCorrespondingDeclaration().getAllAncestors(typeSolver));
            }
        }
        if (wrappedNode.getImplements() != null) {
            for (ClassOrInterfaceType implemented : wrappedNode.getImplements()){
                SymbolReference<TypeDeclaration> superclass = solveType(implemented.getName(), typeSolver);
                if (!superclass.isSolved()) {
                    throw new UnsolvedSymbolException(implemented.getName());
                }
                ancestors.add(superclass.getCorrespondingDeclaration());
                ancestors.addAll(superclass.getCorrespondingDeclaration().getAllAncestors(typeSolver));
            }
        }
        return ancestors;
    }

    @Override
    public List<TypeParameter> getTypeParameters() {
        if (this.wrappedNode.getTypeParameters() == null) {
            return Collections.emptyList();
        } else {
            return this.wrappedNode.getTypeParameters().stream().map(
                    (tp) -> new JavaParserTypeParameter(tp)
            ).collect(Collectors.toList());
        }
    }
}
