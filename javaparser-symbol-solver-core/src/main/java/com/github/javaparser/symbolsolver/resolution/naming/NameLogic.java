package com.github.javaparser.symbolsolver.resolution.naming;

import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.modules.*;
import com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.stmt.TryStmt;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.TypeParameter;

/**
 * NameLogic contains a set of static methods to implement the abstraction of a "Name" as defined
 * in Chapter 6 of the JLS. This code could be moved to an interface or base class in a successive version of
 * JavaParser.
 */
public class NameLogic {

    /**
     * Is the given node a non-qualified name?
     *
     * @throws IllegalArgumentException if the node is not a name
     */
    public static boolean isSimpleName(Node node) {
        return !isQualifiedName(node);
    }

    /**
     * Is the given node a qualified name?
     *
     * @throws IllegalArgumentException if the node is not a name
     */
    public static boolean isQualifiedName(Node node) {
        if (!isAName(node)) {
            throw new IllegalArgumentException();
        }
        return nameAsString(node).contains(".");
    }

    /**
     * Does the Node represent a Name?
     *
     * Note that while most specific AST classes either always represent names or never represent names
     * there are exceptions as the FieldAccessExpr
     */
    public static boolean isAName(Node node) {
        if (node instanceof FieldAccessExpr) {
            FieldAccessExpr fieldAccessExpr = (FieldAccessExpr)node;
            return isAName(fieldAccessExpr.getScope());
        } else {
            return node instanceof SimpleName || node instanceof Name
                    || node instanceof ClassOrInterfaceType || node instanceof NameExpr;
        }
    }

    /**
     * What is the Role of the given name? Does it represent a Declaration or a Reference?
     *
     * This classification is purely syntactical, i.e., it does not require symbol resolution. For this reason in the
     * future this could be moved to the core module of JavaParser.
     */
    public static NameRole classifyRole(Node name) {
        if (!isAName(name)) {
            throw new IllegalArgumentException("The given node is not a name");
        }
        if (!name.getParentNode().isPresent()) {
            throw new IllegalArgumentException("We cannot understand the role of a name if it has no parent");
        }
        if (whenParentIs(Name.class, name, (p, c) -> p.getQualifier().isPresent() && p.getQualifier().get() == c)) {
            return classifyRole(name.getParentNode().get());
        }
        if (whenParentIs(PackageDeclaration.class, name, (p, c) -> p.getName() == c)) {
            return NameRole.DECLARATION;
        }
        if (whenParentIs(ImportDeclaration.class, name, (p, c) -> p.getName() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(MarkerAnnotationExpr.class, name, (p, c) -> p.getName() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(ClassOrInterfaceDeclaration.class, name, (p, c) -> p.getName() == c)) {
            return NameRole.DECLARATION;
        }
        if (whenParentIs(ClassOrInterfaceDeclaration.class, name, (p, c) -> p.getExtendedTypes().contains(c)
                || p.getImplementedTypes().contains(c))) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(ClassOrInterfaceType.class, name, (p, c) -> p.getName() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(VariableDeclarator.class, name, (p, c) -> p.getName() == c)) {
            return NameRole.DECLARATION;
        }
        if (whenParentIs(NameExpr.class, name, (p, c) -> p.getName() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(FieldAccessExpr.class, name, (p, c) -> p.getName() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(AnnotationDeclaration.class, name, (p, c) -> p.getName() == c)) {
            return NameRole.DECLARATION;
        }
        if (whenParentIs(AnnotationMemberDeclaration.class, name, (p, c) -> p.getName() == c)) {
            return NameRole.DECLARATION;
        }
        if (whenParentIs(AnnotationMemberDeclaration.class, name, (p, c) -> p.getType() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(MethodDeclaration.class, name, (p, c) -> p.getName() == c)) {
            return NameRole.DECLARATION;
        }
        if (whenParentIs(MethodDeclaration.class, name, (p, c) -> p.getType() == c || p.getThrownExceptions().contains(c))) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(Parameter.class, name, (p, c) -> p.getName() == c)) {
            return NameRole.DECLARATION;
        }
        if (whenParentIs(Parameter.class, name, (p, c) -> p.getType() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(ReceiverParameter.class, name, (p, c) -> p.getType() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(MethodCallExpr.class, name, (p, c) -> p.getName() == c ||
                (p.getTypeArguments().isPresent() && p.getTypeArguments().get().contains(c)) ||
                (p.getScope().isPresent() && p.getScope().get() == c))) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(ConstructorDeclaration.class, name, (p, c) -> p.getName() == c || p.getThrownExceptions().contains(c))) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(TypeParameter.class, name, (p, c) -> p.getName() == c)) {
            return NameRole.DECLARATION;
        }
        if (whenParentIs(EnumDeclaration.class, name, (p, c) -> p.getName() == c)) {
            return NameRole.DECLARATION;
        }
        if (whenParentIs(EnumConstantDeclaration.class, name, (p, c) -> p.getName() == c)) {
            return NameRole.DECLARATION;
        }
        if (whenParentIs(FieldAccessExpr.class, name, (p, c) -> p.getName() == c || p.getScope() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(ObjectCreationExpr.class, name, (p, c) -> p.getType() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(ReturnStmt.class, name, (p, c) -> p.getExpression().isPresent() && p.getExpression().get() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(ModuleDeclaration.class, name, (p, c) -> p.getName() == c)) {
            return NameRole.DECLARATION;
        }
        if (whenParentIs(ModuleRequiresStmt.class, name, (p, c) -> p.getName() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(ModuleExportsStmt.class, name, (p, c) -> p.getName() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(ModuleExportsStmt.class, name, (p, c) -> p.getModuleNames().contains(c))) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(ModuleOpensStmt.class, name, (p, c) -> p.getName() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(ModuleOpensStmt.class, name, (p, c) -> p.getModuleNames().contains(c))) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(ModuleUsesStmt.class, name, (p, c) -> p.getName() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(ModuleProvidesStmt.class, name, (p, c) -> p.getName() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(ClassExpr.class, name, (p, c) -> p.getType() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(ThisExpr.class, name, (p, c) -> p.getClassExpr().isPresent() && p.getClassExpr().get() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(SuperExpr.class, name, (p, c) -> p.getClassExpr().isPresent() && p.getClassExpr().get() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(VariableDeclarator.class, name, (p, c) -> p.getName() == c)) {
            return NameRole.DECLARATION;
        }
        if (whenParentIs(VariableDeclarator.class, name, (p, c) -> p.getType() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(ArrayCreationExpr.class, name, (p, c) -> p.getElementType() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(CastExpr.class, name, (p, c) -> p.getType() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(InstanceOfExpr.class, name, (p, c) -> p.getType() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(TypeExpr.class, name, (p, c) -> p.getType() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(ArrayAccessExpr.class, name, (p, c) -> p.getName() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(UnaryExpr.class, name, (p, c) -> p.getExpression() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(AssignExpr.class, name, (p, c) -> p.getTarget() == c || p.getValue() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(TryStmt.class, name, (p, c) -> p.getResources().contains(c))) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(VariableDeclarator.class, name, (p, c) -> p.getName() == c)) {
            return NameRole.DECLARATION;
        }
        if (whenParentIs(VariableDeclarator.class, name, (p, c) -> p.getType() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(VariableDeclarator.class, name, (p, c) -> p.getInitializer().isPresent() && p.getInitializer().get() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(MemberValuePair.class, name, (p, c) -> p.getValue() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(MemberValuePair.class, name, (p, c) -> p.getName() == c)) {
            return NameRole.DECLARATION;
        }
        if (whenParentIs(ExplicitConstructorInvocationStmt.class, name, (p, c) ->
                (p.getExpression().isPresent() && p.getExpression().get() == c) ||
                (p.getTypeArguments().isPresent() && p.getTypeArguments().get().contains(c)))) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(ObjectCreationExpr.class, name, (p, c) -> p.getType() == c ||
                (p.getScope().isPresent() && p.getScope().get() == c))) {
            return NameRole.REFERENCE;
        }
        if (name.getParentNode().isPresent() && NameLogic.isAName(name.getParentNode().get())) {
            return classifyRole(name.getParentNode().get());
        }
        throw new UnsupportedOperationException("Unable to classify role of name contained in "
                + name.getParentNode().get().getClass().getSimpleName());
    }

    /**
     * Return the string representation of the name
     */
    public static String nameAsString(Node name) {
        if (!isAName(name)) {
            throw new IllegalArgumentException("A name was expected");
        }
        if (name instanceof Name) {
            return ((Name)name).asString();
        } else if (name instanceof SimpleName) {
            return ((SimpleName) name).getIdentifier();
        } else if (name instanceof ClassOrInterfaceType) {
            return ((ClassOrInterfaceType) name).asString();
        } else if (name instanceof FieldAccessExpr) {
            FieldAccessExpr fieldAccessExpr = (FieldAccessExpr) name;
            if (isAName(fieldAccessExpr.getScope())) {
                return nameAsString(fieldAccessExpr.getScope()) + "." + nameAsString(fieldAccessExpr.getName());
            } else {
                throw new IllegalArgumentException();
            }
        } else if (name instanceof NameExpr) {
            return ((NameExpr)name).getNameAsString();
        } else {
            throw new UnsupportedOperationException("Unknown type of name found: " + name + " ("
                    + name.getClass().getCanonicalName() + ")");
        }
    }

    private interface PredicateOnParentAndChild<P extends Node, C extends Node> {
        boolean isSatisfied(P parent, C child);
    }

    private static <P extends Node, C extends Node> boolean whenParentIs(Class<P> parentClass,
                                                                         C child,
                                                                         PredicateOnParentAndChild<P, C> predicate) {
        if (child.getParentNode().isPresent()) {
            Node parent = child.getParentNode().get();
            return parentClass.isInstance(parent) && predicate.isSatisfied(parentClass.cast(parent), child);
        } else {
            return false;
        }
    }

}
