package me.tomassetti.symbolsolver.javaparser;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;

import java.util.Optional;

/**
 * This class can be used to easily retrieve nodes from a JavaParser AST.
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
            throw new IllegalStateException("No method with given name");
        }
        return found;
    }

    public static VariableDeclarator demandField(ClassOrInterfaceDeclaration cd, String name) {
        for (BodyDeclaration bd : cd.getMembers()) {
            if (bd instanceof FieldDeclaration) {
                FieldDeclaration fd = (FieldDeclaration) bd;
                for (VariableDeclarator vd : fd.getVariables()) {
                    if (vd.getId().getName().equals(name)) {
                        return vd;
                    }
                }
            }
        }
        throw new IllegalStateException("No fieldwith given name");
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

    public static MethodCallExpr findMethodCall(Node node, String methodName) {
        if (node instanceof MethodCallExpr) {
            MethodCallExpr methodCallExpr = (MethodCallExpr) node;
            if (methodCallExpr.getName().equals(methodName)) {
                return methodCallExpr;
            }
        }
        for (Node child : node.getChildrenNodes()) {
            MethodCallExpr res = findMethodCall(child, methodName);
            if (res != null) {
                return res;
            }
        }
        return null;
    }

    public static VariableDeclarator demandVariableDeclaration(Node node, String name) {
        if (node instanceof VariableDeclarator) {
            VariableDeclarator variableDeclarator = (VariableDeclarator)node;
            if (variableDeclarator.getId().getName().equals(name)) {
                return variableDeclarator;
            }
        }
        for (Node child : node.getChildrenNodes()) {
            VariableDeclarator res = demandVariableDeclaration(child, name);
            if (res != null) {
                return res;
            }
        }
        return null;
    }
}
