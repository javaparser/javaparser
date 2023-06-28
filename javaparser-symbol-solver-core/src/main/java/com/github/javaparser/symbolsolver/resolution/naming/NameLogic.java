/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2023 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

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
import com.github.javaparser.resolution.Context;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;

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
     * <p>
     * Note that while most specific AST classes either always represent names or never represent names
     * there are exceptions as the FieldAccessExpr
     */
    public static boolean isAName(Node node) {
        if (node instanceof FieldAccessExpr) {
            FieldAccessExpr fieldAccessExpr = (FieldAccessExpr) node;
            return isAName(fieldAccessExpr.getScope());
        }
        return node instanceof SimpleName ||
                    node instanceof Name ||
                    node instanceof ClassOrInterfaceType ||
                    node instanceof NameExpr;
    }

    private static Node getQualifier(Node node) {
        if (node instanceof FieldAccessExpr) {
            FieldAccessExpr fieldAccessExpr = (FieldAccessExpr) node;
            return fieldAccessExpr.getScope();
        }
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    private static Node getRightMostName(Node node) {
        if (node instanceof FieldAccessExpr) {
            FieldAccessExpr fieldAccessExpr = (FieldAccessExpr) node;
            return fieldAccessExpr.getName();
        }
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    /**
     * What is the Role of the given name? Does it represent a Declaration or a Reference?
     * <p>
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
        if (whenParentIs(PatternExpr.class, name, (p, c) -> p.getName() == c)) {
            return NameRole.DECLARATION;
        }
        if (whenParentIs(PatternExpr.class, name, (p, c) -> p.getType() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(ReceiverParameter.class, name, (p, c) -> p.getType() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(MethodCallExpr.class, name, (p, c) -> p.getName() == c ||
                (p.getTypeArguments().isPresent() && p.getTypeArguments().get().contains(c)) ||
                (p.hasScope() && p.getScope().get() == c))) {
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
        if (whenParentIs(ModuleRequiresDirective.class, name, (p, c) -> p.getName() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(ModuleExportsDirective.class, name, (p, c) -> p.getName() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(ModuleExportsDirective.class, name, (p, c) -> p.getModuleNames().contains(c))) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(ModuleOpensDirective.class, name, (p, c) -> p.getName() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(ModuleOpensDirective.class, name, (p, c) -> p.getModuleNames().contains(c))) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(ModuleUsesDirective.class, name, (p, c) -> p.getName() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(ModuleProvidesDirective.class, name, (p, c) -> p.getName() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(ClassExpr.class, name, (p, c) -> p.getType() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(ThisExpr.class, name, (p, c) -> p.getTypeName().isPresent() && p.getTypeName().get() == c)) {
            return NameRole.REFERENCE;
        }
        if (whenParentIs(SuperExpr.class, name, (p, c) -> p.getTypeName().isPresent() && p.getTypeName().get() == c)) {
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
                (p.hasScope() && p.getScope().get() == c))) {
            return NameRole.REFERENCE;
        }
        if (name.getParentNode().isPresent() && NameLogic.isAName(name.getParentNode().get())) {
            return classifyRole(name.getParentNode().get());
        }
        throw new UnsupportedOperationException("Unable to classify role of name contained in " + name.getParentNode().get().getClass().getSimpleName());
    }

    public static NameCategory classifyReference(Node name, TypeSolver typeSolver) {
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

        if (first.isNeedingDisambiguation()) {
            NameCategory second = reclassificationOfContextuallyAmbiguousNames(name, first, typeSolver);
            assert !second.isNeedingDisambiguation();
            return second;
        }
        return first;
    }

    /**
     * JLS 6.5.2. Reclassification of Contextually Ambiguous Names
     */
    private static NameCategory reclassificationOfContextuallyAmbiguousNames(Node name, NameCategory ambiguousCategory,
                                                                             TypeSolver typeSolver) {
        if (!ambiguousCategory.isNeedingDisambiguation()) {
            throw new IllegalArgumentException("The Name Category is not ambiguous: " + ambiguousCategory);
        }
        if (ambiguousCategory == NameCategory.AMBIGUOUS_NAME && isSimpleName(name)) {
            return reclassificationOfContextuallyAmbiguousSimpleAmbiguousName(name, typeSolver);
        }
        if (ambiguousCategory == NameCategory.AMBIGUOUS_NAME && isQualifiedName(name)) {
            return reclassificationOfContextuallyAmbiguousQualifiedAmbiguousName(name, typeSolver);
        }
        if (ambiguousCategory == NameCategory.PACKAGE_OR_TYPE_NAME) {
            return reclassificationOfContextuallyAmbiguousPackageOrTypeName(name, typeSolver);
        }
        throw new UnsupportedOperationException("I do not know how to handle this semantic reclassification of ambiguous name categories");
    }

    private static NameCategory reclassificationOfContextuallyAmbiguousPackageOrTypeName(Node name, TypeSolver typeSolver) {
        // 6.5.4.1. Simple PackageOrTypeNames
        //
        // If the PackageOrTypeName, Q, is a valid TypeIdentifier and occurs in the scope of a type named Q, then the
        // PackageOrTypeName is reclassified as a TypeName.
        //
        // Otherwise, the PackageOrTypeName is reclassified as a PackageName. The meaning of the PackageOrTypeName is
        // the meaning of the reclassified name.

        if (isSimpleName(name)) {
            if (JavaParserFactory.getContext(name, typeSolver).solveType(nameAsString(name)).isSolved()) {
                return NameCategory.TYPE_NAME;
            }
            return NameCategory.PACKAGE_NAME;
        }

        // 6.5.4.2. Qualified PackageOrTypeNames
        //
        // Given a qualified PackageOrTypeName of the form Q.Id, if Id is a valid TypeIdentifier and the type or package
        // denoted by Q has a member type named Id, then the qualified PackageOrTypeName name is reclassified as a
        // TypeName.
        //
        // Otherwise, it is reclassified as a PackageName. The meaning of the qualified PackageOrTypeName is the meaning
        // of the reclassified name.

        if (isQualifiedName(name)) {
            if (JavaParserFactory.getContext(name, typeSolver).solveType(nameAsString(name)).isSolved()) {
                return NameCategory.TYPE_NAME;
            }
            return NameCategory.PACKAGE_NAME;
        }

        throw new UnsupportedOperationException("This is unexpected: the name is neither simple or qualified");
    }

    private static NameCategory reclassificationOfContextuallyAmbiguousQualifiedAmbiguousName(Node nameNode,
                                                                                              TypeSolver typeSolver) {
        // If the AmbiguousName is a qualified name, consisting of a name, a ".", and an Identifier, then the name to
        // the left of the "." is first reclassified, for it is itself an AmbiguousName. There is then a choice:

        Node leftName = NameLogic.getQualifier(nameNode);
        String rightName = NameLogic.nameAsString(NameLogic.getRightMostName(nameNode));
        NameCategory leftNameCategory = classifyReference(leftName, typeSolver);

        // * If the name to the left of the "." is reclassified as a PackageName, then:
        //
        //      * If the Identifier is a valid TypeIdentifier, and there is a package whose name is the name to the left
        //        of the ".", and that package contains a declaration of a type whose name is the same as the Identifier,
        //        then this AmbiguousName is reclassified as a TypeName.
        //
        //      * Otherwise, this AmbiguousName is reclassified as a PackageName. A later step determines whether or not
        //        a package of that name actually exists.

        if (leftNameCategory == NameCategory.PACKAGE_NAME) {
            if (typeSolver.hasType(nameAsString(nameNode))) {
                return NameCategory.TYPE_NAME;
            }
            return NameCategory.PACKAGE_NAME;
        }

        // * If the name to the left of the "." is reclassified as a TypeName, then:
        //
        //      * If the Identifier is the name of a method or field of the type denoted by TypeName, then this
        //        AmbiguousName is reclassified as an ExpressionName.
        //
        //      * Otherwise, if the Identifier is a valid TypeIdentifier and is the name of a member type of the type
        //        denoted by TypeName, then this AmbiguousName is reclassified as a TypeName.
        //
        //      * Otherwise, a compile-time error occurs.

        if (leftNameCategory == NameCategory.TYPE_NAME) {
            SymbolReference<ResolvedTypeDeclaration> scopeTypeRef = JavaParserFactory.getContext(leftName, typeSolver)
                    .solveType(NameLogic.nameAsString(leftName));
            if (scopeTypeRef.isSolved()) {
                ResolvedTypeDeclaration scopeType = scopeTypeRef.getCorrespondingDeclaration();
                if (scopeType instanceof ResolvedReferenceTypeDeclaration) {
                    ResolvedReferenceTypeDeclaration scopeRefType = scopeType.asReferenceType();
                    if (scopeRefType.getAllMethods().stream().anyMatch(m -> m.getName().equals(rightName))) {
                        return NameCategory.EXPRESSION_NAME;
                    }
                    if (scopeRefType.getAllFields().stream().anyMatch(f -> f.isStatic() && f.getName().equals(rightName))) {
                        return NameCategory.EXPRESSION_NAME;
                    }
                    if (scopeRefType.hasInternalType(rightName)) {
                        return NameCategory.TYPE_NAME;
                    }
                    return NameCategory.COMPILATION_ERROR;
                }
                throw new UnsupportedOperationException("The name is a type but it has been resolved to something that is not a reference type");
            }
            throw new UnsolvedSymbolException("Unable to solve context type: " + NameLogic.nameAsString(leftName));
        }

        // * If the name to the left of the "." is reclassified as an ExpressionName, then this AmbiguousName is
        //   reclassified as an ExpressionName. A later step determines whether or not a member with the name Identifier
        //   actually exists.

        if (leftNameCategory == NameCategory.EXPRESSION_NAME) {
            return NameCategory.EXPRESSION_NAME;
        }

        throw new UnsupportedOperationException("I do not know how to handle this semantic reclassification of ambiguous name categories");
    }

    private static NameCategory reclassificationOfContextuallyAmbiguousSimpleAmbiguousName(Node nameNode,
                                                                                           TypeSolver typeSolver) {
        // If the AmbiguousName is a simple name, consisting of a single Identifier:
        //
        // * If the Identifier appears within the scope (§6.3) of a local variable declaration (§14.4) or parameter
        //   declaration (§8.4.1, §8.8.1, §14.20) or field declaration (§8.3) with that name, then the AmbiguousName is
        //   reclassified as an ExpressionName.

        String name = nameAsString(nameNode);
        Context context = JavaParserFactory.getContext(nameNode, typeSolver);
        if (context.patternExprInScope(name).isPresent()) {
            return NameCategory.EXPRESSION_NAME;
        }
        if (context.localVariableDeclarationInScope(name).isPresent()) {
            return NameCategory.EXPRESSION_NAME;
        }
        if (context.parameterDeclarationInScope(name).isPresent()) {
            return NameCategory.EXPRESSION_NAME;
        }
        if (context.fieldDeclarationInScope(name).isPresent()) {
            return NameCategory.EXPRESSION_NAME;
        }

        // * Otherwise, if a field of that name is declared in the compilation unit (§7.3) containing the Identifier by
        //   a single-static-import declaration (§7.5.3), or by a static-import-on-demand declaration (§7.5.4) then the
        //   AmbiguousName is reclassified as an ExpressionName.
        //
        // * Otherwise, if the Identifier is a valid TypeIdentifier and appears within the scope (§6.3) of a top level
        //   class (§8 (Classes)) or interface type declaration (§9 (Interfaces)), a local class declaration (§14.3) or
        //   member type declaration (§8.5, §9.5) with that name, then the AmbiguousName is reclassified as a TypeName.
        //
        // * Otherwise, if the Identifier is a valid TypeIdentifier and a type of that name is declared in the
        //   compilation unit (§7.3) containing the Identifier, either by a single-type-import declaration (§7.5.1), or
        //   by a type-import-on-demand declaration (§7.5.2), or by a single-static-import declaration (§7.5.3), or by
        //   a static-import-on-demand declaration (§7.5.4), then the AmbiguousName is reclassified as a TypeName.
        //
        // Otherwise, the AmbiguousName is reclassified as a PackageName. A later step determines whether or not a
        // package of that name actually exists.

        return NameCategory.PACKAGE_NAME;
    }

    /**
     * See JLS 6.5.1 Syntactic Classification of a Name According to Context.
     * <p>
     * Most users do not want to call directly this method but call classifyReference instead.
     */
    public static NameCategory syntacticClassificationAccordingToContext(Node name) {

        if (name.getParentNode().isPresent()) {
            Node parent = name.getParentNode().get();
            if (isAName(parent) && nameAsString(name).equals(nameAsString(parent))) {
                return syntacticClassificationAccordingToContext(parent);
            }
        }

        if (isSyntacticallyATypeName(name)) {
            return NameCategory.TYPE_NAME;
        }
        if (isSyntacticallyAnExpressionName(name)) {
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

        if (name instanceof NameExpr) {
            return NameCategory.EXPRESSION_NAME;
        }
        if (name instanceof FieldAccessExpr) {
            return NameCategory.EXPRESSION_NAME;
        }
        if (name instanceof ClassOrInterfaceType) {
            return NameCategory.TYPE_NAME;
        }
        if (name.getParentNode().isPresent() && name.getParentNode().get() instanceof ClassOrInterfaceType) {
            return NameCategory.TYPE_NAME;
        }
        if (name.getParentNode().isPresent() && name.getParentNode().get() instanceof FieldAccessExpr) {
            return NameCategory.EXPRESSION_NAME;
        }

        throw new UnsupportedOperationException("Unable to classify category of name contained in "
                + name.getParentNode().get().getClass().getSimpleName() + ". See " + name + " at " + name.getRange());
    }

    private static boolean isSyntacticallyAAmbiguousName(Node name) {
        // A name is syntactically classified as an AmbiguousName in these contexts:
        //
        // 1. To the left of the "." in a qualified ExpressionName

        if (whenParentIs(FieldAccessExpr.class, name, (p, c) -> p.getScope() == c)) {
            return true;
        }

        // 2. To the left of the rightmost . that occurs before the "(" in a method invocation expression

        if (whenParentIs(MethodCallExpr.class, name, (p, c) -> p.hasScope() && p.getScope().get() == c)) {
            return true;
        }

        // 3. To the left of the "." in a qualified AmbiguousName
        //
        // 4. In the default value clause of an annotation type element declaration (§9.6.2)
        //
        // 5. To the right of an "=" in an element-value pair (§9.7.1)

        if (whenParentIs(MemberValuePair.class, name, (p, c) -> p.getValue() == c)) {
            return true;
        }

        // 6. To the left of :: in a method reference expression (§15.13)
        return false;
    }

    private static boolean isSyntacticallyAPackageOrTypeName(Node name) {
        // A name is syntactically classified as a PackageOrTypeName in these contexts:
        //
        // 1. To the left of the "." in a qualified TypeName

        if (whenParentIs(ClassOrInterfaceType.class, name, (p, c) -> p.getScope().isPresent() && p.getScope().get() == c && (isSyntacticallyATypeName(p) || isSyntacticallyAPackageOrTypeName(p)))) {
            return true;
        }

        // 2. In a type-import-on-demand declaration (§7.5.2)

        if (whenParentIs(ImportDeclaration.class, name, (p, c) ->
                !p.isStatic() && p.isAsterisk() && p.getName() == name)) {
            return true;
        }

        return false;
    }

    private static boolean isSyntacticallyAMethodName(Node name) {
        // A name is syntactically classified as a MethodName in this context:
        //
        // 1. Before the "(" in a method invocation expression (§15.12)

        if (whenParentIs(MethodCallExpr.class, name, (p, c) -> p.getName() == c)) {
            return true;
        }

        return false;
    }

    private static boolean isSyntacticallyAModuleName(Node name) {
        // A name is syntactically classified as a ModuleName in these contexts:
        //
        // 1. In a requires directive in a module declaration (§7.7.1)

        if (whenParentIs(ModuleRequiresDirective.class, name, (p, c) -> p.getName() == name)) {
            return true;
        }

        // 2. To the right of to in an exports or opens directive in a module declaration (§7.7.2)

        if (whenParentIs(ModuleExportsDirective.class, name, (p, c) -> p.getModuleNames().contains(name))) {
            return true;
        }
        if (whenParentIs(ModuleOpensDirective.class, name, (p, c) -> p.getModuleNames().contains(name))) {
            return true;
        }

        return false;
    }

    private static boolean isSyntacticallyAPackageName(Node name) {
        // A name is syntactically classified as a PackageName in these contexts:
        //
        // 1. To the right of exports or opens in a module declaration
        if (whenParentIs(ModuleExportsDirective.class, name, (p, c) -> p.getName() == name)) {
            return true;
        }
        if (whenParentIs(ModuleOpensDirective.class, name, (p, c) -> p.getName() == name)) {
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
        // A name is syntactically classified as a TypeName in these contexts:
        //
        // The first eleven non-generic contexts (§6.1):
        //
        // 1. In a uses or provides directive in a module declaration (§7.7.1)

        if (whenParentIs(ModuleUsesDirective.class, name, (p, c) -> p.getName() == c)) {
            return true;
        }
        if (whenParentIs(ModuleProvidesDirective.class, name, (p, c) -> p.getName() == c)) {
            return true;
        }

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
        if (whenParentIs(ImportDeclaration.class, name, (importDecl, c2) ->
                importDecl.isStatic() && !importDecl.isAsterisk() && importDecl.getName() == c2)) {
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

        if (whenParentIs(ClassExpr.class, name, (p, c) -> p.getType() == c)) {
            return true;
        }

        // 8. To the left of .this in a qualified this expression (§15.8.4)

        if (whenParentIs(ThisExpr.class, name, (ne, c2) ->
                ne.getTypeName().isPresent() && ne.getTypeName().get() == c2)) {
            return true;
        }

        // 9. To the left of .super in a qualified superclass field access expression (§15.11.2)

        if (whenParentIs(SuperExpr.class, name, (ne, c2) ->
                ne.getTypeName().isPresent() && ne.getTypeName().get() == c2)) {
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
        // 2. In an extends clause of an interface declaration (§9.1.3)

        if (whenParentIs(ClassOrInterfaceDeclaration.class, name, (p, c) ->
                p.getExtendedTypes().contains(c) || p.getImplementedTypes().contains(c))) {
            return true;
        }

        // 3. The return type of a method (§8.4, §9.4) (including the type of an element of an annotation type (§9.6.1))

        if (whenParentIs(MethodDeclaration.class, name, (p, c) ->
                p.getType() == c)) {
            return true;
        }
        if (whenParentIs(AnnotationMemberDeclaration.class, name, (p, c) ->
                p.getType() == c)) {
            return true;
        }

        // 4. In the throws clause of a method or constructor (§8.4.6, §8.8.5, §9.4)

        if (whenParentIs(MethodDeclaration.class, name, (p, c) ->
                p.getThrownExceptions().contains(c))) {
            return true;
        }
        if (whenParentIs(ConstructorDeclaration.class, name, (p, c) ->
                p.getThrownExceptions().contains(c))) {
            return true;
        }

        // 5. In an extends clause of a type parameter declaration of a generic class, interface, method, or
        //    constructor (§8.1.2, §9.1.2, §8.4.4, §8.8.4)
        //
        // 6. The type in a field declaration of a class or interface (§8.3, §9.3)

        if (whenParentIs(VariableDeclarator.class, name, (p1, c1) ->
                p1.getType() == c1 && whenParentIs(FieldDeclaration.class, p1, (p2, c2) ->
                        p2.getVariables().contains(c2)))) {
            return true;
        }

        // 7. The type in a formal parameter declaration of a method, constructor, or lambda expression
        //    (§8.4.1, §8.8.1, §9.4, §15.27.1)

        if (whenParentIs(Parameter.class, name, (p, c) ->
                p.getType() == c)) {
            return true;
        }

        // 8. The type of the receiver parameter of a method (§8.4.1)

        if (whenParentIs(ReceiverParameter.class, name, (p, c) ->
                p.getType() == c)) {
            return true;
        }

        // 9. The type in a local variable declaration (§14.4, §14.14.1, §14.14.2, §14.20.3)

        if (whenParentIs(VariableDeclarator.class, name, (p1, c1) ->
                p1.getType() == c1 && whenParentIs(VariableDeclarationExpr.class, p1, (p2, c2) ->
                        p2.getVariables().contains(c2)))) {
            return true;
        }

        // 10. A type in an exception parameter declaration (§14.20)
        //
        // 11. In an explicit type argument list to an explicit constructor invocation statement or class instance
        //     creation expression or method invocation expression (§8.8.7.1, §15.9, §15.12)

        if (whenParentIs(ClassOrInterfaceType.class, name, (p, c) ->
                p.getTypeArguments().isPresent() && p.getTypeArguments().get().contains(c))) {
            return true;
        }
        if (whenParentIs(MethodCallExpr.class, name, (p, c) ->
                p.getTypeArguments().isPresent() && p.getTypeArguments().get().contains(c))) {
            return true;
        }

        // 12. In an unqualified class instance creation expression, either as the class type to be instantiated (§15.9)
        //     or as the direct superclass or direct superinterface of an anonymous class to be instantiated (§15.9.5)

        if (whenParentIs(ObjectCreationExpr.class, name, (p, c) ->
                p.getType() == c)) {
            return true;
        }

        // 13. The element type in an array creation expression (§15.10.1)

        if (whenParentIs(ArrayCreationExpr.class, name, (p, c) ->
                p.getElementType() == c)) {
            return true;
        }

        // 14. The type in the cast operator of a cast expression (§15.16)

        if (whenParentIs(CastExpr.class, name, (p, c) ->
                p.getType() == c)) {
            return true;
        }

        // 15. The type that follows the instanceof relational operator (§15.20.2)

        if (whenParentIs(InstanceOfExpr.class, name, (p, c) ->
                p.getType() == c)) {
            return true;
        }

        // 16. In a method reference expression (§15.13), as the reference type to search for a member method or as the class type or array type to construct.

        if (whenParentIs(TypeExpr.class, name, (p1, c1) ->
                p1.getType() == c1 && whenParentIs(MethodReferenceExpr.class, p1, (p2, c2) ->
                        p2.getScope() == c2)
        )) {
            return true;
        }

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

    private static boolean isSyntacticallyAnExpressionName(Node name) {
        // A name is syntactically classified as an ExpressionName in these contexts:
        //
        // 1. As the qualifying expression in a qualified superclass constructor invocation (§8.8.7.1)

        if (whenParentIs(NameExpr.class, name, (nameExpr, c) ->
                nameExpr.getName() == c && whenParentIs(ExplicitConstructorInvocationStmt.class, nameExpr, (ne, c2) ->
                        ne.getExpression().isPresent() && ne.getExpression().get() == c2)
        )) {
            return true;
        }
        if (whenParentIs(ExplicitConstructorInvocationStmt.class, name, (ne, c2) ->
                ne.getExpression().isPresent() && ne.getExpression().get() == c2)) {
            return true;
        }

        // 2. As the qualifying expression in a qualified class instance creation expression (§15.9)

        if (whenParentIs(NameExpr.class, name, (nameExpr, c) ->
                nameExpr.getName() == c && whenParentIs(ObjectCreationExpr.class, nameExpr, (ne, c2) ->
                        ne.hasScope() && ne.getScope().get() == c2)
        )) {
            return true;
        }
        if (whenParentIs(ObjectCreationExpr.class, name, (ne, c2) ->
                ne.hasScope() && ne.getScope().get() == c2)) {
            return true;
        }

        // 3. As the array reference expression in an array access expression (§15.10.3)

        if (whenParentIs(NameExpr.class, name, (nameExpr, c) ->
                nameExpr.getName() == c && whenParentIs(ArrayAccessExpr.class, nameExpr, (ne, c2) ->
                        ne.getName() == c2)
        )) {
            return true;
        }
        if (whenParentIs(ArrayAccessExpr.class, name, (ne, c2) ->
                ne.getName() == c2)) {
            return true;
        }

        // 4. As a PostfixExpression (§15.14)

        if (whenParentIs(NameExpr.class, name, (nameExpr, c) ->
                nameExpr.getName() == c && whenParentIs(UnaryExpr.class, nameExpr, (ne, c2) ->
                        ne.getExpression() == c2 && ne.isPostfix())
        )) {
            return true;
        }
        if (whenParentIs(UnaryExpr.class, name, (ne, c2) ->
                ne.getExpression() == c2 && ne.isPostfix())) {
            return true;
        }

        // 5. As the left-hand operand of an assignment operator (§15.26)

        if (whenParentIs(NameExpr.class, name, (nameExpr, c) ->
                nameExpr.getName() == c && whenParentIs(AssignExpr.class, nameExpr, (ne, c2) ->
                        ne.getTarget() == c2)
        )) {
            return true;
        }
        if (whenParentIs(AssignExpr.class, name, (ne, c2) ->
                ne.getTarget() == c2)) {
            return true;
        }

        // 6. As a VariableAccess in a try-with-resources statement (§14.20.3)

        if (whenParentIs(NameExpr.class, name, (nameExpr, c) ->
                nameExpr.getName() == c && whenParentIs(TryStmt.class, nameExpr, (ne, c2) ->
                        ne.getResources().contains(c2))
        )) {
            return true;
        }
        if (whenParentIs(NameExpr.class, name, (p1 /*NameExpr*/, c1 /*SimpleName*/) ->
                p1.getName() == c1 && whenParentIs(VariableDeclarator.class, p1, (p2, c2) ->
                        p2.getInitializer().isPresent() && p2.getInitializer().get() == c2 && whenParentIs(VariableDeclarationExpr.class, p2, (p3, c3) ->
                                p3.getVariables().contains(c3) && whenParentIs(TryStmt.class, p3, (p4, c4) ->
                                        p4.getResources().contains(c4)
                                )
                        ))
        )) {
            return true;
        }
        if (whenParentIs(TryStmt.class, name, (ne, c2) ->
                ne.getResources().contains(c2))) {
            return true;
        }
        if (whenParentIs(VariableDeclarator.class, name, (p2, c2) ->
                p2.getInitializer().isPresent() && p2.getInitializer().get() == c2 && whenParentIs(VariableDeclarationExpr.class, p2, (p3, c3) ->
                        p3.getVariables().contains(c3) && whenParentIs(TryStmt.class, p3, (p4, c4) ->
                                p4.getResources().contains(c4)
                        )
                ))) {
            return true;
        }

        return false;
    }

    /**
     * Return the string representation of the name
     */
    public static String nameAsString(Node name) {
        if (!isAName(name)) {
            throw new IllegalArgumentException("A name was expected");
        }
        if (name instanceof Name) {
            return ((Name) name).asString();
        }
            if (name instanceof SimpleName) {
            return ((SimpleName) name).getIdentifier();
        }
            if (name instanceof ClassOrInterfaceType) {
            return ((ClassOrInterfaceType) name).asString();
        }
            if (name instanceof FieldAccessExpr) {
            FieldAccessExpr fieldAccessExpr = (FieldAccessExpr) name;
            if (isAName(fieldAccessExpr.getScope())) {
                return nameAsString(fieldAccessExpr.getScope()) + "." + nameAsString(fieldAccessExpr.getName());
            }
            throw new IllegalArgumentException();
        }
            if (name instanceof NameExpr) {
            return ((NameExpr) name).getNameAsString();
        }
        throw new UnsupportedOperationException("Unknown type of name found: " + name + " ("
                    + name.getClass().getCanonicalName() + ")");
    }

    private interface PredicateOnParentAndChild<P extends Node, C extends Node> {
        boolean isSatisfied(P parent, C child);
    }

    private static <P extends Node, C extends Node> boolean whenParentIs(Class<P> parentClass, C child) {
        return whenParentIs(parentClass, child, (p, c) -> true);
    }

    private static <P extends Node, C extends Node> boolean whenParentIs(
            Class<P> parentClass,
            C child,
            PredicateOnParentAndChild<P, C> predicate) {
        if (child.getParentNode().isPresent()) {
            Node parent = child.getParentNode().get();
            return parentClass.isInstance(parent) && predicate.isSatisfied(parentClass.cast(parent), child);
        }
        return false;
    }

}
