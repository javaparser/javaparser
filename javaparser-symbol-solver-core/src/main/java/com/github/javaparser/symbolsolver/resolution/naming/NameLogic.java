package com.github.javaparser.symbolsolver.resolution.naming;

import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.modules.ModuleExportsStmt;
import com.github.javaparser.ast.modules.ModuleOpensStmt;
import com.github.javaparser.ast.modules.ModuleRequiresStmt;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.TypeParameter;

public class NameLogic {

    public static boolean isAName(Node node) {
        return node instanceof SimpleName || node instanceof Name || node instanceof ClassOrInterfaceType;
    }

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
        if (whenParentIs(MethodDeclaration.class, name, (p, c) -> p.getName() == c)) {
            return NameRole.DECLARATION;
        }
        if (whenParentIs(Parameter.class, name, (p, c) -> p.getName() == c)) {
            return NameRole.DECLARATION;
        }
        if (whenParentIs(MethodCallExpr.class, name, (p, c) -> p.getName() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(ConstructorDeclaration.class, name, (p, c) -> p.getName() == c)) {
            return NameRole.DECLARATION;
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
        throw new UnsupportedOperationException("Unable to classify role of name contained in "+ name.getParentNode().get().getClass().getSimpleName());
    }

    public static NameCategory classifyReference(Node name) {
        if (!name.getParentNode().isPresent()) {
            throw new IllegalArgumentException("We cannot understand the category of a name if it has no parent");
        }
        if (classifyRole(name) != NameRole.REFERENCE) {
            throw new IllegalArgumentException("This method can be used only to classify names used as references");
        }

        // JLS 6.5
        // First, context causes a name syntactically to fall into one of seven categories: ModuleName, PackageName,
        // TypeName, ExpressionName, MethodName, PackageOrTypeName, or AmbiguousName.

        NameCategory first = syntacticClassificationAccordingToContext(name);

        // Second, a name that is initially classified by its context as an AmbiguousName or as a PackageOrTypeName is
        // then reclassified to be a PackageName, TypeName, or ExpressionName.
        if (first.isNeedingDisambiguation()) {
            NameCategory second = reclassificationOfContextuallyAmbiguousNames(name, first);
            assert !second.isNeedingDisambiguation();
            return second;
        } else {
            return first;
        }
    }

    /**
     * JLS 6.5.2. Reclassification of Contextually Ambiguous Names
     */
    private static NameCategory reclassificationOfContextuallyAmbiguousNames(Node name, NameCategory ambiguousCategory) {
        if (!ambiguousCategory.isNeedingDisambiguation()) {
            throw new IllegalArgumentException("The Name Category is not ambiguous: " + ambiguousCategory);
        }
        throw new UnsupportedOperationException();
    }

    /**
     * See JLS 6.5.1 Syntactic Classification of a Name According to Context.
     *
     * Most users do not want to call directly this method but call classifyReference instead.
     */
    public static NameCategory syntacticClassificationAccordingToContext(Node name) {
        if (isSyntacticallyATypeName(name)) {
            return NameCategory.TYPE_NAME;
        }
        if (isSyntacticallyAExpressionName(name)) {
            return NameCategory.EXPRESSION_NAME;
        }
        if (isSyntacticallyAMethodName(name)) {
            return NameCategory.METHOD_NAME;
        }
        if (isSyntacticallyAPackageOrTypeName(name)) {
            return NameCategory.PACKAGE_OR_TYPE_NAME;
        }
        if (isSyntacticallyAAmbiguousName(name)) {
            return NameCategory.AMBIGUOUS_NAME;
        }
        if (isSyntacticallyAModuleName(name)) {
            return NameCategory.MODULE_NAME;
        }
        if (isSyntacticallyAPackageName(name)) {
            return NameCategory.PACKAGE_NAME;
        }

        throw new UnsupportedOperationException("Unable to classify category of name contained in "
                + name.getParentNode().get().getClass().getSimpleName());
    }

    private static boolean isSyntacticallyAAmbiguousName(Node name) {
        // A name is syntactically classified as an AmbiguousName in these contexts:
        //
        // 1. To the left of the "." in a qualified ExpressionName
        //
        // 2. To the left of the rightmost . that occurs before the "(" in a method invocation expression
        //
        // 3. To the left of the "." in a qualified AmbiguousName
        //
        // 4. In the default value clause of an annotation type element declaration (§9.6.2)
        //
        // 5. To the right of an "=" in an an element-value pair (§9.7.1)
        //
        // 6. To the left of :: in a method reference expression (§15.13)
        return false;
    }

    private static boolean isSyntacticallyAPackageOrTypeName(Node name) {
        // A name is syntactically classified as a PackageOrTypeName in these contexts:
        //
        // 1. To the left of the "." in a qualified TypeName
        //
        // 2. In a type-import-on-demand declaration (§7.5.2)
        return false;
    }

    private static boolean isSyntacticallyAMethodName(Node name) {
        // A name is syntactically classified as a MethodName in this context:
        //
        // 1. Before the "(" in a method invocation expression (§15.12)
        return false;
    }

    private static boolean isSyntacticallyAModuleName(Node name) {
        // A name is syntactically classified as a ModuleName in these contexts:
        //
        // 1. In a requires directive in a module declaration (§7.7.1)

        if (whenParentIs(ModuleRequiresStmt.class, name, (p, c) -> p.getName() == name)) {
            return true;
        }

        // 2. To the right of to in an exports or opens directive in a module declaration (§7.7.2)

        if (whenParentIs(ModuleExportsStmt.class, name, (p, c) -> p.getModuleNames().contains(name))) {
            return true;
        }
        if (whenParentIs(ModuleOpensStmt.class, name, (p, c) -> p.getModuleNames().contains(name))) {
            return true;
        }

        return false;
    }

    private static boolean isSyntacticallyAPackageName(Node name) {
        // A name is syntactically classified as a PackageName in these contexts:
        //
        // 1. To the right of exports or opens in a module declaration
        if (whenParentIs(ModuleExportsStmt.class, name, (p, c) -> p.getName() == name)) {
            return true;
        }
        if (whenParentIs(ModuleOpensStmt.class, name, (p, c) -> p.getName() == name)) {
            return true;
        }
        // 2. To the left of the "." in a qualified PackageName
        if (whenParentIs(Name.class, name, (p, c) -> p.getQualifier().isPresent()
                && p.getQualifier().get() == name
                && isSyntacticallyAPackageName(p))) {
            return true;
        }
        return false;
    }

    private static boolean isSyntacticallyATypeName(Node name) {

        if (name instanceof ClassOrInterfaceType
                || whenParentIs(ClassOrInterfaceType.class, name)) {
            return true;
        }

        // A name is syntactically classified as a TypeName in these contexts:
        //
        // The first eleven non-generic contexts (§6.1):
        //
        // 1. In a uses or provides directive in a module declaration (§7.7.1)
        //
        // 2. In a single-type-import declaration (§7.5.1)

        if (whenParentIs(ImportDeclaration.class, name, (p, c) ->
                !p.isStatic() && !p.isAsterisk() && p.getName() == name)) {
            return true;
        }

        // 3. To the left of the . in a single-static-import declaration (§7.5.3)

        if (whenParentIs(Name.class, name, (largerName, c) ->
           whenParentIs(ImportDeclaration.class, largerName, (importDecl, c2) ->
                   importDecl.isStatic() && !importDecl.isAsterisk() && importDecl.getName() == c2)
        )) {
            return true;
        }

        // 4. To the left of the . in a static-import-on-demand declaration (§7.5.4)

        if (whenParentIs(ImportDeclaration.class, name, (p, c) ->
                p.isStatic() && p.isAsterisk() && p.getName() == name)) {
            return true;
        }

        // 5. To the left of the ( in a constructor declaration (§8.8)

        if (whenParentIs(ConstructorDeclaration.class, name, (p, c) -> p.getName() == name)) {
            return true;
        }

        // 6. After the @ sign in an annotation (§9.7)

        if (whenParentIs(AnnotationExpr.class, name, (p, c) -> p.getName() == name)) {
            return true;
        }

        // 7. To the left of .class in a class literal (§15.8.2)
        //
        // 8. To the left of .this in a qualified this expression (§15.8.4)

        if (whenParentIs(NameExpr.class, name, (nameExpr, c) ->
                nameExpr.getName() == c && whenParentIs(ThisExpr.class, nameExpr, (ne, c2) ->
                        ne.getClassExpr().isPresent() && ne.getClassExpr().get() == c2)
        )) {
            return true;
        }

        // 9. To the left of .super in a qualified superclass field access expression (§15.11.2)

        if (whenParentIs(NameExpr.class, name, (nameExpr, c) ->
                nameExpr.getName() == c && whenParentIs(SuperExpr.class, nameExpr, (ne, c2) ->
                        ne.getClassExpr().isPresent() && ne.getClassExpr().get() == c2)
        )) {
            return true;
        }

        // 10. To the left of .Identifier or .super.Identifier in a qualified method invocation expression (§15.12)
        //
        // 11. To the left of .super:: in a method reference expression (§15.13)
        //
        // As the Identifier or dotted Identifier sequence that constitutes any ReferenceType (including a
        // ReferenceType to the left of the brackets in an array type, or to the left of the < in a parameterized type,
        // or in a non-wildcard type argument of a parameterized type, or in an extends or super clause of a wildcard
        // type argument of a parameterized type) in the 16 contexts where types are used (§4.11):
        //
        // 1. In an extends or implements clause of a class declaration (§8.1.4, §8.1.5, §8.5, §9.5)
        //
        // 2. In an extends clause of an interface declaration (§9.1.3)
        //
        // 3. The return type of a method (§8.4, §9.4) (including the type of an element of an annotation type (§9.6.1))
        //
        // 4. In the throws clause of a method or constructor (§8.4.6, §8.8.5, §9.4)
        //
        // 5. In an extends clause of a type parameter declaration of a generic class, interface, method, or
        //    constructor (§8.1.2, §9.1.2, §8.4.4, §8.8.4)
        //
        // 6. The type in a field declaration of a class or interface (§8.3, §9.3)
        //
        // 7. The type in a formal parameter declaration of a method, constructor, or lambda expression
        //    (§8.4.1, §8.8.1, §9.4, §15.27.1)
        //
        // 8. The type of the receiver parameter of a method (§8.4.1)
        //
        // 9. The type in a local variable declaration (§14.4, §14.14.1, §14.14.2, §14.20.3)
        //
        // 10. A type in an exception parameter declaration (§14.20)
        //
        // 11. In an explicit type argument list to an explicit constructor invocation statement or class instance
        //     creation expression or method invocation expression (§8.8.7.1, §15.9, §15.12)
        //
        // 12. In an unqualified class instance creation expression, either as the class type to be instantiated (§15.9)
        //     or as the direct superclass or direct superinterface of an anonymous class to be instantiated (§15.9.5)
        //
        // 13. The element type in an array creation expression (§15.10.1)
        //
        // 14. The type in the cast operator of a cast expression (§15.16)
        //
        // 15. The type that follows the instanceof relational operator (§15.20.2)
        //
        // 16. In a method reference expression (§15.13), as the reference type to search for a member method or as the class type or array type to construct.
        //
        // The extraction of a TypeName from the identifiers of a ReferenceType in the 16 contexts above is intended to
        // apply recursively to all sub-terms of the ReferenceType, such as its element type and any type arguments.
        //
        // For example, suppose a field declaration uses the type p.q.Foo[]. The brackets of the array type are ignored,
        // and the term p.q.Foo is extracted as a dotted sequence of Identifiers to the left of the brackets in an array
        // type, and classified as a TypeName. A later step determines which of p, q, and Foo is a type name or a
        // package name.
        //
        // As another example, suppose a cast operator uses the type p.q.Foo<? extends String>. The term p.q.Foo is
        // again extracted as a dotted sequence of Identifier terms, this time to the left of the < in a parameterized
        // type, and classified as a TypeName. The term String is extracted as an Identifier in an extends clause of a
        // wildcard type argument of a parameterized type, and classified as a TypeName.
        return false;
    }

    private static boolean isSyntacticallyAExpressionName(Node name) {
        // A name is syntactically classified as an ExpressionName in these contexts:
        //
        // 1. As the qualifying expression in a qualified superclass constructor invocation (§8.8.7.1)
        //
        // 2. As the qualifying expression in a qualified class instance creation expression (§15.9)
        //
        // 3. As the array reference expression in an array access expression (§15.10.3)
        //
        // 4. As a PostfixExpression (§15.14)
        //
        // 5. As the left-hand operand of an assignment operator (§15.26)
        //
        // 6. As a VariableAccess in a try-with-resources statement (§14.20.3)
        return false;
    }

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
        } else {
            throw new UnsupportedOperationException("Unknown type of name found: " + name + " ("
                    + name.getClass().getCanonicalName() + ")");
        }
    }

    private interface PredicateOnParentAndChild<P extends Node, C extends Node> {
        boolean isSatisfied(P parent, C child);
    }

    private static <P extends Node, C extends Node> boolean whenParentIs(Class<P> parentClass,
                                                                         C child) {
        return whenParentIs(parentClass, child, (p, c) -> true);
    }

    private static <P extends Node, C extends Node> boolean whenParentIs(Class<P> parentClass,
                                                                         C child,
                                                                         PredicateOnParentAndChild<P, C> predicate) {
        if (child.getParentNode().isPresent()) {
            Node parent = child.getParentNode().get();
            if (parentClass.isInstance(parent)) {
                return predicate.isSatisfied(parentClass.cast(parent), child);
            } else {
                return false;
            }
        } else {
            return false;
        }
    }

}
