package me.tomassetti.symbolsolver.javaparser;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.stmt.SwitchStmt;

import java.util.Optional;

/**
 * This class can be used to easily retrieve nodes from a JavaParser AST.
 */
public final class Navigator {

    private Navigator() {
        // prevent instantiation
    }

    public static Optional<TypeDeclaration> findType(CompilationUnit cu, String name) {
        if (cu.getTypes() == null) {
            return Optional.empty();
        }
        
        String[] nameParts = name.split("\\.", 2);
        final String typeName = nameParts[0];
        
        Optional<TypeDeclaration> type = cu.getTypes().stream().filter((t) -> t.getName().equals(typeName)).findFirst();
        
        if (nameParts.length > 1 && type.isPresent()) {
            return findType(type.get(), nameParts[1]);
        } 
        return type;
    }
    
    public static Optional<TypeDeclaration> findType(TypeDeclaration td, String name) {
        String[] nameParts = name.split("\\.", 2);
        
        Optional<TypeDeclaration> type = Optional.empty();
        for (Node n: td.getChildrenNodes()) {
            if (n instanceof TypeDeclaration && ((TypeDeclaration)n).getName().equals(nameParts[0])) {
                type = Optional.of((TypeDeclaration)n);
                break;
            }
        }
        if (nameParts.length > 1 && type.isPresent()) {
            return findType(type.get(), nameParts[1]);
        } 
        return type;
    }
    

    public static ClassOrInterfaceDeclaration demandClass(CompilationUnit cu, String name) {
        ClassOrInterfaceDeclaration cd = demandClassOrInterface(cu, name);
        if (cd.isInterface()) {
            throw new IllegalStateException("Type is not a class");
        }
        return cd;
    }

    public static EnumDeclaration demandEnum(CompilationUnit cu, String name) {
        Optional<TypeDeclaration> res = findType(cu, name);
        if (!res.isPresent()) {
            throw new IllegalStateException("No type found");
        }
        if (!(res.get() instanceof EnumDeclaration)) {
            throw new IllegalStateException("Type is not an enum");
        }
        return (EnumDeclaration) res.get();
    }

    public static MethodDeclaration demandMethod(ClassOrInterfaceDeclaration cd, String name) {
        MethodDeclaration found = null;
        for (BodyDeclaration bd : cd.getMembers()) {
            if (bd instanceof MethodDeclaration) {
                MethodDeclaration md = (MethodDeclaration) bd;
                if (md.getName().equals(name)) {
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
        throw new IllegalStateException("No field with given name");
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
            VariableDeclarator variableDeclarator = (VariableDeclarator) node;
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

    public static ClassOrInterfaceDeclaration demandClassOrInterface(CompilationUnit compilationUnit, String name) {
        Optional<TypeDeclaration> res = findType(compilationUnit, name);
        if (!res.isPresent()) {
            throw new IllegalStateException("No type named '" + name + "'found");
        }
        if (!(res.get() instanceof ClassOrInterfaceDeclaration)) {
            throw new IllegalStateException("Type is not a class or an interface, it is " + res.get().getClass().getCanonicalName());
        }
        ClassOrInterfaceDeclaration cd = (ClassOrInterfaceDeclaration) res.get();
        return cd;
    }

    public static SwitchStmt findSwitch(Node node) {
        SwitchStmt res = findSwitchHelper(node);
        if (res == null) {
            throw new IllegalArgumentException();
        } else {
            return res;
        }
    }

    private static SwitchStmt findSwitchHelper(Node node) {
        if (node instanceof SwitchStmt) {
            return (SwitchStmt) node;
        }
        for (Node child : node.getChildrenNodes()) {
            SwitchStmt resChild = findSwitchHelper(child);
            if (resChild != null) {
                return resChild;
            }
        }
        return null;
    }

    private static <N> N findNodeOfGivenClasshHelper(Node node, Class<N> clazz) {
        if (clazz.isInstance(node)) {
            return clazz.cast(node);
        }
        for (Node child : node.getChildrenNodes()) {
            N resChild = findNodeOfGivenClasshHelper(child, clazz);
            if (resChild != null) {
                return resChild;
            }
        }
        return null;
    }

    public static <N> N findNodeOfGivenClass(Node node, Class<N> clazz) {
        N res = findNodeOfGivenClasshHelper(node, clazz);
        if (res == null) {
            throw new IllegalArgumentException();
        } else {
            return res;
        }
    }

    public static ReturnStmt findReturnStmt(MethodDeclaration method) {
        return findNodeOfGivenClass(method, ReturnStmt.class);
    }
}
