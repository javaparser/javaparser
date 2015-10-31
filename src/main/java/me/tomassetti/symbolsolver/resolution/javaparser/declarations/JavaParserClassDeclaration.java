package me.tomassetti.symbolsolver.resolution.javaparser.declarations;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.Type;
import me.tomassetti.symbolsolver.JavaParserFacade;
import me.tomassetti.symbolsolver.resolution.*;
import me.tomassetti.symbolsolver.model.declarations.FieldDeclaration;
import me.tomassetti.symbolsolver.model.declarations.*;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.resolution.javaparser.JavaParserFactory;
import me.tomassetti.symbolsolver.resolution.javaparser.UnsolvedSymbolException;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import me.tomassetti.symbolsolver.model.typesystem.ReferenceTypeUsage;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by federico on 30/07/15.
 */
public class JavaParserClassDeclaration implements ClassDeclaration {

    private TypeSolver typeSolver;

    public JavaParserClassDeclaration(com.github.javaparser.ast.body.ClassOrInterfaceDeclaration wrappedNode,
                                      TypeSolver typeSolver) {
        if (wrappedNode.isInterface()) {
            throw new IllegalArgumentException("Interface given");
        }
        this.wrappedNode = wrappedNode;
        this.typeSolver = typeSolver;
    }

    private com.github.javaparser.ast.body.ClassOrInterfaceDeclaration wrappedNode;

    @Override
    public Context getContext() {
        return JavaParserFactory.getContext(wrappedNode, typeSolver);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        JavaParserClassDeclaration that = (JavaParserClassDeclaration) o;

        if (!wrappedNode.equals(that.wrappedNode)) return false;

        return true;
    }

    @Override
    public int hashCode() {
        return wrappedNode.hashCode();
    }

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
            return typeSolver.getRoot().solveType("java.lang.Object").asType().asClass();
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
    public boolean isAssignableBy(TypeDeclaration other) {
        List<ReferenceTypeUsage> ancestorsOfOther = other.getAllAncestors();
        ancestorsOfOther.add(new ReferenceTypeUsage(other, typeSolver));
        for (ReferenceTypeUsage ancestorOfOther : ancestorsOfOther) {
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
    public boolean isAssignableBy(TypeUsage typeUsage) {
        if (typeUsage.isNull()) {
            return true;
        }
        if (typeUsage.isReferenceType()){
            TypeDeclaration other = typeSolver.solveType(typeUsage.describe());
            return isAssignableBy(other);
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
        ClassDeclaration superclass = getSuperClass(typeSolver);
        if (superclass != null) {
            if (superclass.canBeAssignedTo(other, typeSolver)) {
                return true;
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

        ClassDeclaration superclass = this.getSuperClass(typeSolver);
        if (superclass != null) {
            return superclass.getField(name, typeSolver);
        } else {
            throw new UnsolvedSymbolException("In class " + this, name);
        }

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

        ClassDeclaration superclass = this.getSuperClass(typeSolver);
        if (superclass != null) {
            return superclass.hasField(name, typeSolver);
        } else {
            return false;
        }
    }

    @Override
    public SymbolReference<? extends ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        //throw new UnsupportedOperationException("Solving symbol " + name);
        return SymbolReference.unsolved(ValueDeclaration.class);
    }

    @Override
    public SymbolReference<TypeDeclaration> solveType(String name, TypeSolver typeSolver) {
        if (this.wrappedNode.getName().equals(name)){
            return SymbolReference.solved(this);
        }
        if (this.wrappedNode.getTypeParameters() != null) {
            for (com.github.javaparser.ast.TypeParameter typeParameter : this.wrappedNode.getTypeParameters()) {
                if (typeParameter.getName().equals(name)) {
                    return SymbolReference.solved(new JavaParserTypeVariableDeclaration(typeParameter, typeSolver));
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
                        return SymbolReference.solved(new JavaParserClassDeclaration((com.github.javaparser.ast.body.ClassOrInterfaceDeclaration) internalType, typeSolver));
                    } else if (internalType instanceof EnumDeclaration) {
                        return SymbolReference.solved(new JavaParserEnumDeclaration((com.github.javaparser.ast.body.EnumDeclaration) internalType, typeSolver));
                    } else {
                        throw new UnsupportedOperationException();
                    }
                } else if (name.startsWith(prefix) && name.length() > prefix.length()) {
                    if (internalType instanceof ClassOrInterfaceDeclaration) {
                        return new JavaParserClassDeclaration((com.github.javaparser.ast.body.ClassOrInterfaceDeclaration) internalType, typeSolver).solveType(name.substring(prefix.length()), typeSolver);
                    } else if (internalType instanceof EnumDeclaration) {
                        return new JavaParserEnumDeclaration((com.github.javaparser.ast.body.EnumDeclaration) internalType, typeSolver).solveType(name.substring(prefix.length()), typeSolver);
                    } else {
                        throw new UnsupportedOperationException();
                    }
                }
            }
        }

        String prefix = wrappedNode.getName() + ".";
        if (name.startsWith(prefix) && name.length() > prefix.length()){
            return new JavaParserClassDeclaration(this.wrappedNode, typeSolver).solveType(name.substring(prefix.length()), typeSolver);
        }

        //return SymbolReference.unsolved(TypeDeclaration.class);
        return getContext().getParent().solveType(name, typeSolver);
    }

    @Override
    public List<ReferenceTypeUsage> getAllAncestors() {
        List<ReferenceTypeUsage> ancestors = new ArrayList<>();
        ClassDeclaration superclass = getSuperClass(typeSolver);
        if (superclass != null) {
            ancestors.add(new ReferenceTypeUsage(superclass, typeSolver));
            ancestors.addAll(superclass.getAllAncestors());
        }
        if (wrappedNode.getImplements() != null) {
            for (ClassOrInterfaceType implemented : wrappedNode.getImplements()){
                ReferenceTypeUsage ancestor = toTypeUsage(implemented, typeSolver);
                ancestors.add(ancestor);
                ancestors.addAll(ancestor.getAllAncestors());
            }
        }
        return ancestors;
    }

    private ReferenceTypeUsage toTypeUsage(ClassOrInterfaceType type, TypeSolver typeSolver){
        SymbolReference<TypeDeclaration> ancestor = solveType(type.getName(), typeSolver.getRoot());
        if (!ancestor.isSolved()) {
            throw new UnsolvedSymbolException(type.getName());
        }
        if (type.getTypeArgs() != null) {
            List<TypeUsage> typeParams = type.getTypeArgs().stream().map((t)->toTypeUsage(t, typeSolver)).collect(Collectors.toList());
            return new ReferenceTypeUsage(ancestor.getCorrespondingDeclaration(), typeParams, typeSolver);
        } else {
            return new ReferenceTypeUsage(ancestor.getCorrespondingDeclaration(), typeSolver);
        }
    }

    private TypeUsage toTypeUsage(Type type, TypeSolver typeSolver){
        return JavaParserFacade.get(typeSolver).convert(type, type);
    }

    @Override
    public List<TypeParameter> getTypeParameters() {
        if (this.wrappedNode.getTypeParameters() == null) {
            return Collections.emptyList();
        } else {
            return this.wrappedNode.getTypeParameters().stream().map(
                    (tp) -> new JavaParserTypeParameter(tp, typeSolver)
            ).collect(Collectors.toList());
        }
    }
}
