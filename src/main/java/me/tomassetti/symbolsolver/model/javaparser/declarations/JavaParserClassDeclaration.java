package me.tomassetti.symbolsolver.model.javaparser.declarations;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.body.*;
import me.tomassetti.symbolsolver.model.*;
import me.tomassetti.symbolsolver.model.FieldDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ClassDeclaration;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.javaparser.JavaParserFactory;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;

import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by federico on 30/07/15.
 */
public class JavaParserClassDeclaration implements ClassDeclaration {

    public JavaParserClassDeclaration(ClassOrInterfaceDeclaration wrappedNode) {
        this.wrappedNode = wrappedNode;
    }

    private ClassOrInterfaceDeclaration wrappedNode;

    @Override
    public Context getContext() {
        return JavaParserFactory.getContext(wrappedNode);
    }

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
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
    public boolean isType() {
        return true;
    }

    /*@Override
    public TypeDeclaration asTypeDeclaration() {
        return this;
    }

    @Override
    public TypeDeclaration getType() {
        throw new UnsupportedOperationException();
    }*/

    @Override
    public String getQualifiedName() {
        String containerName = containerName("", wrappedNode.getParentNode());
        if (containerName.isEmpty()) {
            return wrappedNode.getName();
        } else {
            return containerName + "." + wrappedNode.getName();
        }
    }

    private String containerName(String base, Node container) {
        if (container instanceof ClassOrInterfaceDeclaration) {
            String b = containerName(base, container.getParentNode());
            String cn = ((ClassOrInterfaceDeclaration)container).getName();
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

    /*@Override
    public TypeUsage getUsage(Node node) {
        return new TypeUsageOfTypeDeclaration(getType());
    }*/

    @Override
    public boolean isAssignableBy(TypeUsage typeUsage) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isTypeVariable() {
        return false;
    }

    @Override
    public FieldDeclaration getField(String name) {
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
    public boolean hasField(String name) {
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
