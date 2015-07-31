package me.tomassetti.symbolsolver.javaparser;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.expr.NameExpr;

import java.util.Optional;

/**
 * This class can be used to conveniently retrieve certain node from a JavaParser AST.
 */
public final class Navigator {

    private Navigator() {
        // prevent instantiation
    }

    public static Optional<TypeDeclaration> findType(CompilationUnit cu, String name) {
        return cu.getTypes().stream().filter((t)->t.getName().equals(name)).findFirst();
    }

    public static ClassOrInterfaceDeclaration demandClass(CompilationUnit cu, String name) {
        Optional<TypeDeclaration> res = findType(cu, name);
        if (!res.isPresent()) {
            throw new IllegalStateException("No type found");
        }
        if (!(res.get() instanceof ClassOrInterfaceDeclaration)){
            throw new IllegalStateException("Type is not a class");
        }
        ClassOrInterfaceDeclaration cd = (ClassOrInterfaceDeclaration)res.get();
        if (cd.isInterface()) {
            throw new IllegalStateException("Type is not a class");
        }
        return cd;
    }

    public static MethodDeclaration demandMethod(ClassOrInterfaceDeclaration cd, String name) {
        MethodDeclaration found = null;
        for (BodyDeclaration bd : cd.getMembers()) {
            if (bd instanceof MethodDeclaration) {
                MethodDeclaration md = (MethodDeclaration)bd;
                if (md.getName().equals(name)){
                    if (found != null) {
                        throw new IllegalStateException("Ambiguous getName");
                    }
                    found = md;
                }
            }
        }
        if (found == null) {
            throw new IllegalStateException("No method with given getName");
        }
        return found;
    }

    public static NameExpr findNameExpression(Node node, String name) {
        if (node instanceof NameExpr) {
            NameExpr nameExpr = (NameExpr) node;
            if (nameExpr.getName().equals(name)) {
                return nameExpr;
            }
        }
        for (Node child : node.getChildrenNodes()) {
            NameExpr res = findNameExpression(child, name);
            if (res != null) {
                return res;
            }
        }
        return null;
    }
}
