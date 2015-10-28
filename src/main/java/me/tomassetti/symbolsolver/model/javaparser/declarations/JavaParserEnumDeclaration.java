package me.tomassetti.symbolsolver.model.javaparser.declarations;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.EnumConstantDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import me.tomassetti.symbolsolver.model.*;
import me.tomassetti.symbolsolver.model.declarations.*;
import me.tomassetti.symbolsolver.model.javaparser.JavaParserFactory;
import me.tomassetti.symbolsolver.model.javaparser.UnsolvedSymbolException;
import me.tomassetti.symbolsolver.model.typesystem.ArrayTypeUsage;
import me.tomassetti.symbolsolver.model.typesystem.MethodUsage;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import me.tomassetti.symbolsolver.model.typesystem.ReferenceTypeUsage;

import java.io.Serializable;
import java.util.Collections;
import java.util.List;
import java.util.Optional;

/**
 * Created by federico on 30/07/15.
 */
public class JavaParserEnumDeclaration implements EnumDeclaration {

    public JavaParserEnumDeclaration(com.github.javaparser.ast.body.EnumDeclaration wrappedNode) {
        this.wrappedNode = wrappedNode;
    }

    private com.github.javaparser.ast.body.EnumDeclaration wrappedNode;

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
    public boolean canBeAssignedTo(TypeDeclaration other, TypeSolver typeSolver) {
        // Enums cannot be extended
        if (other.getQualifiedName().equals(this.getQualifiedName())) {
            return true;
        }
        if (other.getQualifiedName().equals(Enum.class.getCanonicalName())) {
            return true;
        }
        // Enum implements Comparable and Serializable
        if (other.getQualifiedName().equals(Comparable.class.getCanonicalName())) {
            return true;
        }
        if (other.getQualifiedName().equals(Serializable.class.getCanonicalName())) {
            return true;
        }
        if (other.getQualifiedName().equals(Object.class.getCanonicalName())) {
            return true;
        }
        return false;
    }

    @Override
    public boolean isClass() {
        return false;
    }

    @Override
    public boolean isInterface() {
        return false;
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
        return typeUsage.getQualifiedName().equals(getQualifiedName());
    }

    @Override
    public boolean isTypeVariable() {
        return false;
    }

    @Override
    public FieldDeclaration getField(String name, TypeSolver typeSolver) {
        if (this.wrappedNode.getMembers() != null) {
            for (BodyDeclaration member : this.wrappedNode.getMembers()) {
                if (member instanceof com.github.javaparser.ast.body.FieldDeclaration) {
                    com.github.javaparser.ast.body.FieldDeclaration field = (com.github.javaparser.ast.body.FieldDeclaration) member;
                    for (VariableDeclarator vd : field.getVariables()) {
                        if (vd.getId().getName().equals(name)) {
                            return new JavaParserFieldDeclaration(vd);
                        }
                    }
                }
            }
        }

        if (this.wrappedNode.getEntries() != null) {
            for (EnumConstantDeclaration member : this.wrappedNode.getEntries()) {
                if (member.getName().equals(name)) {
                    return new JavaParserFieldDeclaration(member);
                }
            }
        }

        throw new UnsolvedSymbolException("Field "+name);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        JavaParserEnumDeclaration that = (JavaParserEnumDeclaration) o;

        if (!wrappedNode.equals(that.wrappedNode)) return false;

        return true;
    }

    @Override
    public int hashCode() {
        return wrappedNode.hashCode();
    }

    private class ValuesMethod implements MethodDeclaration {

        @Override
        public TypeDeclaration declaringType() {
            throw new UnsupportedOperationException();
        }

        @Override
        public TypeUsage getReturnType(TypeSolver typeSolver) {
            return new ArrayTypeUsage(new ReferenceTypeUsage(JavaParserEnumDeclaration.this));
        }

        @Override
        public int getNoParams() {
            return 0;
        }

        @Override
        public ParameterDeclaration getParam(int i) {
            throw new UnsupportedOperationException();
        }

        @Override
        public MethodUsage getUsage(Node node) {
            throw new UnsupportedOperationException();
        }

        @Override
        public MethodUsage resolveTypeVariables(Context context, TypeSolver typeSolver, List<TypeUsage> parameterTypes) {
            return new MethodUsage(this, typeSolver);
        }

        @Override
        public Context getContext() {
            throw new UnsupportedOperationException();
        }

        @Override
        public String getName() {
            return "values";
        }

        @Override
        public List<TypeParameter> getTypeParameters() {
            return Collections.emptyList();
        }
    }

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver) {
        if (name.equals("values") && parameterTypes.size() == 0) {
            return SymbolReference.solved(new ValuesMethod());
        }
        // TODO add methods inherited from Enum
        return getContext().solveMethod(name, parameterTypes, typeSolver);
    }

    @Override
    public Optional<MethodUsage> solveMethodAsUsage(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver, Context invokationContext, List<TypeUsage> typeParameterValues) {
        if (name.equals("values") && parameterTypes.size() == 0) {
            return Optional.of(new ValuesMethod().getUsage(null));
        }
        // TODO add methods inherited from Enum
        return getContext().solveMethodAsUsage(name, parameterTypes, typeSolver);
    }

    @Override
    public boolean hasField(String name, TypeSolver typeSolver) {
        if (this.wrappedNode.getMembers() != null) {
            for (BodyDeclaration member : this.wrappedNode.getMembers()) {
                if (member instanceof com.github.javaparser.ast.body.FieldDeclaration) {
                    com.github.javaparser.ast.body.FieldDeclaration field = (com.github.javaparser.ast.body.FieldDeclaration) member;
                    for (VariableDeclarator vd : field.getVariables()) {
                        if (vd.getId().getName().equals(name)) {
                            return true;
                        }
                    }
                }
            }

        }

        if (this.wrappedNode.getEntries() != null) {
            for (EnumConstantDeclaration member : this.wrappedNode.getEntries()) {
                if (member.getName().equals(name)) {
                    return true;
                }
            }
        }

        return false;
    }

    @Override
    public SymbolReference<? extends ValueDeclaration> solveSymbol(String substring, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }

    @Override
    public SymbolReference<TypeDeclaration> solveType(String substring, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<ReferenceTypeUsage> getAllAncestors(TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<TypeParameter> getTypeParameters() {
        return Collections.emptyList();
    }
}
