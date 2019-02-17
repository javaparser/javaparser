/*
 * Copyright 2016 Federico Tomassetti
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.github.javaparser.symbolsolver.javaparser;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.stmt.SwitchStmt;

import java.util.List;
import java.util.Optional;

/**
 * This class can be used to easily retrieve nodes from a JavaParser AST.
 *
 * @author Federico Tomassetti
 */
public final class Navigator {

    private Navigator() {
        // prevent instantiation
    }

    public static Node requireParentNode(Node node) {
        return node.getParentNode().orElseThrow(() -> new IllegalStateException("Parent not found, the node does not appear to be inserted in a correct AST"));
    }

    /**
     * Looks among the type declared in the Compilation Unit for one having the specified name.
     * The name can be qualified with respect to the compilation unit. For example, if the compilation
     * unit is in package a.b; and it contains two top level classes named C and D, with class E being defined inside D
     * then the qualifiedName that can be resolved are "C", "D", and "D.E".
     */
    public static Optional<TypeDeclaration<?>> findType(CompilationUnit cu, String qualifiedName) {
        if (cu.getTypes().isEmpty()) {
            return Optional.empty();
        }

        final String typeName = getOuterTypeName(qualifiedName);
        Optional<TypeDeclaration<?>> type = cu.getTypes().stream().filter((t) -> t.getName().getId().equals(typeName)).findFirst();

        final String innerTypeName = getInnerTypeName(qualifiedName);
        if (type.isPresent() && !innerTypeName.isEmpty()) {
            return findType(type.get(), innerTypeName);
        }
        return type;
    }

    /**
     * Looks among the type declared in the TypeDeclaration for one having the specified name.
     * The name can be qualified with respect to the TypeDeclaration. For example, if the class declarationd defines class D
     * and class D contains an internal class named E then the qualifiedName that can be resolved are "D", and "D.E".
     */
    public static Optional<TypeDeclaration<?>> findType(TypeDeclaration<?> td, String qualifiedName) {
        final String typeName = getOuterTypeName(qualifiedName);

        Optional<TypeDeclaration<?>> type = Optional.empty();
        for (Node n : td.getMembers()) {
            if (n instanceof TypeDeclaration && ((TypeDeclaration<?>) n).getName().getId().equals(typeName)) {
                type = Optional.of((TypeDeclaration<?>) n);
                break;
            }
        }
        final String innerTypeName = getInnerTypeName(qualifiedName);
        if (type.isPresent() && !innerTypeName.isEmpty()) {
            return findType(type.get(), innerTypeName);
        }
        return type;
    }

    public static ClassOrInterfaceDeclaration demandClass(CompilationUnit cu, String qualifiedName) {
        ClassOrInterfaceDeclaration cd = demandClassOrInterface(cu, qualifiedName);
        if (cd.isInterface()) {
            throw new IllegalStateException("Type is not a class");
        }
        return cd;
    }

    public static ClassOrInterfaceDeclaration demandInterface(CompilationUnit cu, String qualifiedName) {
        ClassOrInterfaceDeclaration cd = demandClassOrInterface(cu, qualifiedName);
        if (!cd.isInterface()) {
            throw new IllegalStateException("Type is not an interface");
        }
        return cd;
    }

    public static EnumDeclaration demandEnum(CompilationUnit cu, String qualifiedName) {
        Optional<TypeDeclaration<?>> res = findType(cu, qualifiedName);
        if (!res.isPresent()) {
            throw new IllegalStateException("No type found");
        }
        if (!(res.get() instanceof EnumDeclaration)) {
            throw new IllegalStateException("Type is not an enum");
        }
        return (EnumDeclaration) res.get();
    }

    public static MethodDeclaration demandMethod(TypeDeclaration<?> cd, String name) {
        MethodDeclaration found = null;
        for (BodyDeclaration<?> bd : cd.getMembers()) {
            if (bd instanceof MethodDeclaration) {
                MethodDeclaration md = (MethodDeclaration) bd;
                if (md.getNameAsString().equals(name)) {
                    if (found != null) {
                        throw new IllegalStateException("Ambiguous getName");
                    }
                    found = md;
                }
            }
        }
        if (found == null) {
            throw new IllegalStateException("No method called " + name);
        }
        return found;
    }

    /**
     * Returns the {@code (i+1)}'th constructor of the given type declaration, in textual order. The constructor that
     * appears first has the index 0, the second one the index 1, and so on.
     *
     * @param td    The type declaration to search in. Note that only classes and enums have constructors.
     * @param index The index of the desired constructor.
     * @return The desired ConstructorDeclaration if it was found, and {@code null} otherwise.
     */
    public static ConstructorDeclaration demandConstructor(TypeDeclaration<?> td, int index) {
        ConstructorDeclaration found = null;
        int i = 0;
        for (BodyDeclaration<?> bd : td.getMembers()) {
            if (bd instanceof ConstructorDeclaration) {
                ConstructorDeclaration cd = (ConstructorDeclaration) bd;
                if (i == index) {
                    found = cd;
                    break;
                }
                i++;
            }
        }
        if (found == null) {
            throw new IllegalStateException("No constructor with index " + index);
        }
        return found;
    }

    public static VariableDeclarator demandField(ClassOrInterfaceDeclaration cd, String name) {
        for (BodyDeclaration<?> bd : cd.getMembers()) {
            if (bd instanceof FieldDeclaration) {
                FieldDeclaration fd = (FieldDeclaration) bd;
                for (VariableDeclarator vd : fd.getVariables()) {
                    if (vd.getName().getId().equals(name)) {
                        return vd;
                    }
                }
            }
        }
        throw new IllegalStateException("No field with given name");
    }

    public static Optional<NameExpr> findNameExpression(Node node, String name) {
        return node.findFirst(NameExpr.class, n -> n.getNameAsString().equals(name));
    }

    public static Optional<SimpleName> findSimpleName(Node node, String name) {
        return node.findFirst(SimpleName.class, n -> n.asString().equals(name));
    }


    public static Optional<MethodCallExpr> findMethodCall(Node node, String methodName) {
        return node.findFirst(MethodCallExpr.class, n -> n.getNameAsString().equals(methodName));
    }

    public static Optional<VariableDeclarator> demandVariableDeclaration(Node node, String name) {
        return node.findFirst(VariableDeclarator.class, n -> n.getNameAsString().equals(name));
    }

    public static ClassOrInterfaceDeclaration demandClassOrInterface(CompilationUnit compilationUnit, String qualifiedName) {
        return findType(compilationUnit, qualifiedName)
                .map(res -> res.toClassOrInterfaceDeclaration().orElseThrow(() -> new IllegalStateException("Type is not a class or an interface, it is " + res.getClass().getCanonicalName())))
                .orElseThrow(() -> new IllegalStateException("No type named '" + qualifiedName + "'found"));
    }

    // TODO should be demand or requireSwitch
    public static SwitchStmt findSwitch(Node node) {
        return findSwitchHelper(node).orElseThrow(IllegalArgumentException::new);
    }

    public static <N extends Node> N findNodeOfGivenClass(Node node, Class<N> clazz) {
        return node.findFirst(clazz).orElseThrow(IllegalArgumentException::new);
    }

    // TODO should be demand or require...
    public static ReturnStmt findReturnStmt(MethodDeclaration method) {
        return findNodeOfGivenClass(method, ReturnStmt.class);
    }

    ///
    /// Private methods
    ///

    private static String getOuterTypeName(String qualifiedName) {
        return qualifiedName.split("\\.", 2)[0];
    }

    private static String getInnerTypeName(String qualifiedName) {
        if (qualifiedName.contains(".")) {
            return qualifiedName.split("\\.", 2)[1];
        }
        return "";
    }

    private static Optional<SwitchStmt> findSwitchHelper(Node node) {
        // TODO can be replaced by findFirst with the correct algorithm.
        if (node instanceof SwitchStmt) {
            return Optional.of((SwitchStmt) node);
        }
        for (Node child : node.getChildNodes()) {
            Optional<SwitchStmt> resChild = findSwitchHelper(child);
            if (resChild.isPresent()) {
                return resChild;
            }
        }
        return Optional.empty();
    }
}
