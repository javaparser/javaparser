/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
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

package com.github.javaparser.printer;

import com.github.javaparser.ASTParserConstants;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.expr.ClassExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.printer.concretesyntaxmodel.*;

import java.util.*;
import java.util.function.Function;
import java.util.function.Predicate;

import static com.github.javaparser.ast.observer.ObservableProperty.*;
import static com.github.javaparser.utils.PositionUtils.sortByBeginPosition;

/**
 * The Concrete Syntax Model for a single node type. It knows the syntax used to represent a certain element in Java
 * code.
 */
public class ConcreteSyntaxModel {

    CsmElement topElement;

    static Map<Class, ConcreteSyntaxModel> concreteSyntaxModelByClass = new HashMap<>();

    static {
        concreteSyntaxModelByClass.put(CompilationUnit.class, new Builder().comment()
                    .child(ObservableProperty.PACKAGE_DECLARATION)
                    .list(ObservableProperty.IMPORTS, newline())
                    .list(TYPES, newline())
                    .orphanCommentsEnding()
                    .build());
//
//        concreteSyntaxModelByClass.put(PackageDeclaration.class, new Builder()
//                .comment().property(ObservableProperty.ANNOTATIONS).token(ASTParserConstants.PACKAGE, "package").token(ASTParserConstants.EOF, " ").property(ObservableProperty.NAME).token(ASTParserConstants.SEMICOLON, ";").newline().newline().orphanCommentsEnding()
//                .build());
//
//        concreteSyntaxModelByClass.put(NameExpr.class, new Builder()
//                .comment().property(ObservableProperty.NAME).orphanCommentsEnding()
//                .build());
//
//        concreteSyntaxModelByClass.put(Name.class, new Builder()
//                .comment().conditional(ObservableProperty.QUALIFIER, IS_PRESENT,.property(ObservableProperty.QUALIFIER).token(ASTParserConstants.DOT, "."), null).value(ObservableProperty.IDENTIFIER).orphanCommentsEnding()
//                .build());
//
        concreteSyntaxModelByClass.put(SimpleName.class, new Builder()
                .value(ObservableProperty.IDENTIFIER)
                .build());

        concreteSyntaxModelByClass.put(ClassOrInterfaceDeclaration.class, new Builder().comment()
                    .list(ObservableProperty.ANNOTATIONS, newline(), null, newline())
                    .modifiers()
                    .ifThenElse(node -> ((ClassOrInterfaceDeclaration)node).isInterface(), string(ASTParserConstants.INTERFACE), string(ASTParserConstants.CLASS))
                    .space()
                    .child(ObservableProperty.NAME)
                    .list(TYPE_PARAMETERS, sequence(comma(), space()), string(ASTParserConstants.LT), string(ASTParserConstants.GT))
                    .list(ObservableProperty.EXTENDED_TYPES, sequence(
                            space(),
                            string(ASTParserConstants.EXTENDS),
                            space()), null, sequence(string(ASTParserConstants.COMMA), space()))
                    .list(ObservableProperty.IMPLEMENTED_TYPES, sequence(
                            space(),
                            string(ASTParserConstants.IMPLEMENTS),
                            space()), null, sequence(string(ASTParserConstants.COMMA), space()))
                    .space()
                    .block(list(ObservableProperty.MEMBERS, null, null, newline()))
                    .newline()
                    .build());
//
//        concreteSyntaxModelByClass.put(JavadocComment.class, new Builder()
//                .token(ASTParserConstants.SLASH, "/").token(ASTParserConstants.STAR, "*").token(ASTParserConstants.STAR, "*")/* printer.print(n.getContent()); */.token(ASTParserConstants.JAVA_DOC_COMMENT, "*/").newline()
//                .build());
//
        concreteSyntaxModelByClass.put(ClassOrInterfaceType.class, new Builder().comment()
                    .ifThen(SCOPE, sequence(child(SCOPE), string(ASTParserConstants.DOT)))
                    .list(ANNOTATIONS, space())
                    .child(NAME)
                    .ifThenElse(node -> ((ClassOrInterfaceType)node).isUsingDiamondOperator(),
                            sequence(string(ASTParserConstants.LT), string(ASTParserConstants.GT)),
                            list(TYPE_ARGUMENTS, sequence(comma(), space()), string(ASTParserConstants.LT), string(ASTParserConstants.GT)))
                    .build());
//
//        concreteSyntaxModelByClass.put(TypeParameter.class, new Builder()
//                .comment()/* for (AnnotationExpr ann : n.getAnnotations()) {
//    ann.accept(this, arg);
//    printer.print(" ");
//} */.property(ObservableProperty.NAME).conditional(ObservableProperty.TYPE_BOUND, IS_NOT_EMPTY,.token(ASTParserConstants.EOF, " ").token(ASTParserConstants.EXTENDS, "extends").token(ASTParserConstants.EOF, " ")/* for (final Iterator<ClassOrInterfaceType> i = n.getTypeBound().iterator(); i.hasNext(); ) {
//    final ClassOrInterfaceType c = i.next();
//    c.accept(this, arg);
//    if (i.hasNext()) {
//        printer.print(" & ");
//    }
//} */, null)
//                .build());
//
        concreteSyntaxModelByClass.put(PrimitiveType.class, new Builder()
                    .comment()
                    .annotations()
                    .value(ObservableProperty.TYPE)
                    .build());
//
        concreteSyntaxModelByClass.put(ArrayType.class, new Builder()
                    .child(ObservableProperty.COMPONENT_TYPE)
                    .list(ObservableProperty.ANNOTATIONS)
                    .string(ASTParserConstants.LBRACKET)
                    .string(ASTParserConstants.RBRACKET)
                    .build());
//
//        concreteSyntaxModelByClass.put(ArrayCreationLevel.class, new Builder()
//                .property(ObservableProperty.ANNOTATIONS).token(ASTParserConstants.LBRACKET, "[").conditional(ObservableProperty.DIMENSION, IS_PRESENT,.property(ObservableProperty.DIMENSION), null).token(ASTParserConstants.RBRACKET, "]")
//                .build());
//
//        concreteSyntaxModelByClass.put(IntersectionType.class, new Builder()
//                .comment().property(ObservableProperty.ANNOTATIONS)/* boolean isFirst = true; *//* for (ReferenceType element : n.getElements()) {
//    element.accept(this, arg);
//    if (isFirst) {
//        isFirst = false;
//    } else {
//        printer.print(" & ");
//    }
//} */
//                .build());
//
//        concreteSyntaxModelByClass.put(UnionType.class, new Builder()
//                .comment().property(ObservableProperty.ANNOTATIONS)/* boolean isFirst = true; *//* for (ReferenceType element : n.getElements()) {
//    if (isFirst) {
//        isFirst = false;
//    } else {
//        printer.print(" | ");
//    }
//    element.accept(this, arg);
//} */
//                .build());
//
//        concreteSyntaxModelByClass.put(WildcardType.class, new Builder()
//                .comment().property(ObservableProperty.ANNOTATIONS).token(ASTParserConstants.HOOK, "?").conditional(ObservableProperty.EXTENDED_TYPES, IS_PRESENT,.token(ASTParserConstants.EOF, " ").token(ASTParserConstants.EXTENDS, "extends").token(ASTParserConstants.EOF, " ").property(ObservableProperty.EXTENDED_TYPES), null).conditional(ObservableProperty.SUPER, IS_PRESENT,.token(ASTParserConstants.EOF, " ").token(ASTParserConstants.SUPER, "super").token(ASTParserConstants.EOF, " ").property(ObservableProperty.SUPER), null)
//.build());
//
//        concreteSyntaxModelByClass.put(UnknownType.class, new Builder()
//
//                .build());
//
        concreteSyntaxModelByClass.put(FieldDeclaration.class, new Builder()
                    .orphanCommentsBeforeThis()
                    .comment()
                    .annotations()
                    .modifiers()
                    .ifThen(ObservableProperty.VARIABLES, function(node -> child(ObservableProperty.MAXIMUM_COMMON_TYPE)))
                    .space()
                    .list(ObservableProperty.VARIABLES, sequence(comma(), space(), null, null))
                    .semicolon()
                    .build());

        concreteSyntaxModelByClass.put(VariableDeclarator.class, new Builder()
                    .comment()
                    .child(ObservableProperty.NAME)
                    .build());
//
//        concreteSyntaxModelByClass.put(ArrayInitializerExpr.class, new Builder()
//                .comment().token(ASTParserConstants.LBRACE, "{").conditional(ObservableProperty.VALUES, IS_NOT_EMPTY,.token(ASTParserConstants.EOF, " ")/* for (final Iterator<Expression> i = n.getValues().iterator(); i.hasNext(); ) {
//    final Expression expr = i.next();
//    expr.accept(this, arg);
//    if (i.hasNext()) {
//        printer.print(", ");
//    }
//} */.token(ASTParserConstants.EOF, " "), null).token(ASTParserConstants.RBRACE, "}")
//                .build());
//
//        concreteSyntaxModelByClass.put(VoidType.class, new Builder()
//                .comment().property(ObservableProperty.ANNOTATIONS).token(ASTParserConstants.VOID, "void")
//                .build());
//
//        concreteSyntaxModelByClass.put(ArrayAccessExpr.class, new Builder()
//                .comment().property(ObservableProperty.NAME).token(ASTParserConstants.LBRACKET, "[").property(ObservableProperty.INDEX).token(ASTParserConstants.RBRACKET, "]")
//                .build());
//
//        concreteSyntaxModelByClass.put(ArrayCreationExpr.class, new Builder()
//                .comment().token(ASTParserConstants.NEW, "new").token(ASTParserConstants.EOF, " ").property(ObservableProperty.ELEMENT_TYPE)/* for (ArrayCreationLevel level : n.getLevels()) {
//    level.accept(this, arg);
//} */.conditional(ObservableProperty.INITIALIZER, IS_PRESENT,.token(ASTParserConstants.EOF, " ").property(ObservableProperty.INITIALIZER), null)
//                .build());
//
//        concreteSyntaxModelByClass.put(AssignExpr.class, new Builder()
//                .comment().property(ObservableProperty.TARGET).token(ASTParserConstants.EOF, " ")/* printer.print(n.getOperator().asString()); */.token(ASTParserConstants.EOF, " ").property(ObservableProperty.VALUE)
//                .build());
//
//        concreteSyntaxModelByClass.put(BinaryExpr.class, new Builder()
//                .comment().property(ObservableProperty.LEFT).token(ASTParserConstants.EOF, " ")/* printer.print(n.getOperator().asString()); */.token(ASTParserConstants.EOF, " ").property(ObservableProperty.RIGHT)
//                .build());
//
//        concreteSyntaxModelByClass.put(CastExpr.class, new Builder()
//                .comment().token(ASTParserConstants.LPAREN, "(").property(ObservableProperty.TYPE).token(ASTParserConstants.RPAREN, ")").token(ASTParserConstants.EOF, " ").property(ObservableProperty.EXPRESSION)
//                .build());
//
        concreteSyntaxModelByClass.put(ClassExpr.class, new Builder()
                .comment().property(ObservableProperty.TYPE).token(ASTParserConstants.DOT, ".").token(ASTParserConstants.CLASS, "class")
                .build());
//
//        concreteSyntaxModelByClass.put(ConditionalExpr.class, new Builder()
//                .comment().property(ObservableProperty.CONDITION).token(ASTParserConstants.EOF, " ").token(ASTParserConstants.HOOK, "?").token(ASTParserConstants.EOF, " ").property(ObservableProperty.THEN_EXPR).token(ASTParserConstants.EOF, " ").token(ASTParserConstants.COLON, ":").token(ASTParserConstants.EOF, " ").property(ObservableProperty.ELSE_EXPR)
//                .build());
//
//        concreteSyntaxModelByClass.put(EnclosedExpr.class, new Builder()
//                .comment().token(ASTParserConstants.LPAREN, "(").conditional(ObservableProperty.INNER, IS_PRESENT,.property(ObservableProperty.INNER), null).token(ASTParserConstants.RPAREN, ")")
//                .build());
//
//        concreteSyntaxModelByClass.put(FieldAccessExpr.class, new Builder()
//                .comment().conditional(ObservableProperty.SCOPE, IS_PRESENT,.property(ObservableProperty.SCOPE), null).token(ASTParserConstants.DOT, ".").property(ObservableProperty.NAME)
//                .build());
//
//        concreteSyntaxModelByClass.put(InstanceOfExpr.class, new Builder()
//                .comment().property(ObservableProperty.EXPRESSION).token(ASTParserConstants.EOF, " ").token(ASTParserConstants.INSTANCEOF, "instanceof").token(ASTParserConstants.EOF, " ").property(ObservableProperty.TYPE)
//                .build());
//
//        concreteSyntaxModelByClass.put(CharLiteralExpr.class, new Builder()
//                .comment()/* printer.print("'"); *//* printer.print(n.getValue()); *//* printer.print("'"); */
//                .build());
//
//        concreteSyntaxModelByClass.put(DoubleLiteralExpr.class, new Builder()
//                .comment()/* printer.print(n.getValue()); */
//                .build());
//
//        concreteSyntaxModelByClass.put(IntegerLiteralExpr.class, new Builder()
//                .comment()/* printer.print(n.getValue()); */
//                .build());
//
//        concreteSyntaxModelByClass.put(LongLiteralExpr.class, new Builder()
//                .comment()/* printer.print(n.getValue()); */
//                .build());
//
//        concreteSyntaxModelByClass.put(StringLiteralExpr.class, new Builder()
//                .comment()/* printer.print("\""); *//* printer.print(n.getValue()); *//* printer.print("\""); */
//                .build());
//
//        concreteSyntaxModelByClass.put(BooleanLiteralExpr.class, new Builder()
//                .comment()/* printer.print(String.valueOf(n.getValue())); */
//                .build());
//
//        concreteSyntaxModelByClass.put(NullLiteralExpr.class, new Builder()
//                .comment().token(ASTParserConstants.NULL, "null")
//                .build());
//
//        concreteSyntaxModelByClass.put(ThisExpr.class, new Builder()
//                .comment().conditional(ObservableProperty.CLASS_EXPR, IS_PRESENT,.property(ObservableProperty.CLASS_EXPR).token(ASTParserConstants.DOT, "."), null).token(ASTParserConstants.THIS, "this")
//                .build());
//
//        concreteSyntaxModelByClass.put(SuperExpr.class, new Builder()
//                .comment().conditional(ObservableProperty.CLASS_EXPR, IS_PRESENT,.property(ObservableProperty.CLASS_EXPR).token(ASTParserConstants.DOT, "."), null).token(ASTParserConstants.SUPER, "super")
//                .build());
//
//        concreteSyntaxModelByClass.put(MethodCallExpr.class, new Builder()
//                .comment().conditional(ObservableProperty.SCOPE, IS_PRESENT,.property(ObservableProperty.SCOPE).token(ASTParserConstants.DOT, "."), null).property(ObservableProperty.TYPE_ARGUMENTS).property(ObservableProperty.NAME).property(ObservableProperty.ARGUMENTS)
//                .build());
//
//        concreteSyntaxModelByClass.put(ObjectCreationExpr.class, new Builder()
//                .comment().conditional(ObservableProperty.SCOPE, IS_PRESENT,.property(ObservableProperty.SCOPE).token(ASTParserConstants.DOT, "."), null).token(ASTParserConstants.NEW, "new").token(ASTParserConstants.EOF, " ").property(ObservableProperty.TYPE_ARGUMENTS)/* if (!isNullOrEmpty(n.getTypeArguments().orElse(null))) {
//    printer.print(" ");
//} */.property(ObservableProperty.TYPE).property(ObservableProperty.ARGUMENTS).conditional(ObservableProperty.ANONYMOUS_CLASS_BODY, IS_PRESENT,.token(ASTParserConstants.EOF, " ").token(ASTParserConstants.LBRACE, "{").newline().indent().property(ObservableProperty.MEMBERS).unindent().token(ASTParserConstants.RBRACE, "}"), null)
//.build());
//
//        concreteSyntaxModelByClass.put(UnaryExpr.class, new Builder()
//                .comment()/* if (n.getOperator().isPrefix()) {
//    printer.print(n.getOperator().asString());
//} */.property(ObservableProperty.EXPRESSION)/* if (n.getOperator().isPostfix()) {
//    printer.print(n.getOperator().asString());
//} */
//                .build());
//
//        concreteSyntaxModelByClass.put(ConstructorDeclaration.class, new Builder()
//                .comment().property(ObservableProperty.ANNOTATIONS).property(ObservableProperty.MODIFIERS)/* printTypeParameters(n.getTypeParameters(), arg); *//* if (n.isGeneric()) {
//    printer.print(" ");
//} */.property(ObservableProperty.NAME).token(ASTParserConstants.LPAREN, "(").conditional(ObservableProperty.PARAMETERS, IS_NOT_EMPTY,/* for (final Iterator<Parameter> i = n.getParameters().iterator(); i.hasNext(); ) {
//    final Parameter p = i.next();
//    p.accept(this, arg);
//    if (i.hasNext()) {
//        printer.print(", ");
//    }
//} */, null).token(ASTParserConstants.RPAREN, ")").conditional(ObservableProperty.THROWN_TYPES, IS_NOT_EMPTY,.token(ASTParserConstants.EOF, " ").token(ASTParserConstants.THROWS, "throws").token(ASTParserConstants.EOF, " ")/* for (final Iterator<ReferenceType> i = n.getThrownExceptions().iterator(); i.hasNext(); ) {
//    final ReferenceType name = i.next();
//    name.accept(this, arg);
//    if (i.hasNext()) {
//        printer.print(", ");
//    }
//} */, null).token(ASTParserConstants.EOF, " ").property(ObservableProperty.BODY)
//                .build());
//
//        concreteSyntaxModelByClass.put(MethodDeclaration.class, new Builder()
//                .orphanCommentsBeforeThis().comment().property(ObservableProperty.ANNOTATIONS).property(ObservableProperty.MODIFIERS)/* if (n.isDefault()) {
//    printer.print("default ");
//} *//* printTypeParameters(n.getTypeParameters(), arg); */.conditional(ObservableProperty.TYPE_PARAMETERS, IS_NOT_EMPTY,.token(ASTParserConstants.EOF, " "), null).property(ObservableProperty.TYPE).token(ASTParserConstants.EOF, " ").property(ObservableProperty.NAME).token(ASTParserConstants.LPAREN, "(").conditional(ObservableProperty.PARAMETERS, IS_NOT_EMPTY,/* for (final Iterator<Parameter> i = n.getParameters().iterator(); i.hasNext(); ) {
//    final Parameter p = i.next();
//    p.accept(this, arg);
//    if (i.hasNext()) {
//        printer.print(", ");
//    }
//} */, null).token(ASTParserConstants.RPAREN, ")").conditional(ObservableProperty.THROWN_TYPES, IS_NOT_EMPTY,.token(ASTParserConstants.EOF, " ").token(ASTParserConstants.THROWS, "throws").token(ASTParserConstants.EOF, " ")/* for (final Iterator<ReferenceType> i = n.getThrownExceptions().iterator(); i.hasNext(); ) {
//    final ReferenceType name = i.next();
//    name.accept(this, arg);
//    if (i.hasNext()) {
//        printer.print(", ");
//    }
//} */, null)/* if (!n.getBody().isPresent()) {
//    printer.print(";");
//} else {
//    printer.print(" ");
//    n.getBody().get().accept(this, arg);
//} */
//.build());
//
//        concreteSyntaxModelByClass.put(Parameter.class, new Builder()
//                .comment().property(ObservableProperty.ANNOTATIONS).property(ObservableProperty.MODIFIERS)/* if (n.getType() != null) {
//    n.getType().accept(this, arg);
//} */.conditional(ObservableProperty.VAR_ARGS, ATTRIBUTE_VALUE,.token(ASTParserConstants.ELLIPSIS, "..."), null).token(ASTParserConstants.EOF, " ").property(ObservableProperty.NAME)
//                .build());
//
//        concreteSyntaxModelByClass.put(ExplicitConstructorInvocationStmt.class, new Builder()
//                .comment()/* if (n.isThis()) {
//    printTypeArgs(n, arg);
//    printer.print("this");
//} else {
//    if (n.getExpression().isPresent()) {
//        n.getExpression().get().accept(this, arg);
//        printer.print(".");
//    }
//    printTypeArgs(n, arg);
//    printer.print("super");
//} */.property(ObservableProperty.ARGUMENTS).token(ASTParserConstants.SEMICOLON, ";")
//                .build());
//
//        concreteSyntaxModelByClass.put(VariableDeclarationExpr.class, new Builder()
//                .comment().property(ObservableProperty.ANNOTATIONS).property(ObservableProperty.MODIFIERS).conditional(ObservableProperty.VARIABLES, IS_NOT_EMPTY,/* getMaximumCommonType(n).accept(this, arg); */, null).token(ASTParserConstants.EOF, " ")/* for (final Iterator<VariableDeclarator> i = n.getVariables().iterator(); i.hasNext(); ) {
//    final VariableDeclarator v = i.next();
//    v.accept(this, arg);
//    if (i.hasNext()) {
//        printer.print(", ");
//    }
//} */
//                .build());
//
//        concreteSyntaxModelByClass.put(LocalClassDeclarationStmt.class, new Builder()
//                .comment().property(ObservableProperty.CLASS_DECLARATION)
//                .build());
//
//        concreteSyntaxModelByClass.put(AssertStmt.class, new Builder()
//                .comment().token(ASTParserConstants.ASSERT, "assert").token(ASTParserConstants.EOF, " ").property(ObservableProperty.CHECK).conditional(ObservableProperty.MESSAGE, IS_PRESENT,.token(ASTParserConstants.EOF, " ").token(ASTParserConstants.COLON, ":").token(ASTParserConstants.EOF, " ").property(ObservableProperty.MESSAGE), null).token(ASTParserConstants.SEMICOLON, ";")
//                .build());
//
//        concreteSyntaxModelByClass.put(BlockStmt.class, new Builder()
//                .orphanCommentsBeforeThis().comment().token(ASTParserConstants.LBRACE, "{").newline()/* if (n.getStatements() != null) {
//    printer.indent();
//    for (final Statement s : n.getStatements()) {
//        s.accept(this, arg);
//        printer.println();
//    }
//    printer.unindent();
//} */.orphanCommentsEnding().token(ASTParserConstants.RBRACE, "}")
//                .build());
//
//        concreteSyntaxModelByClass.put(LabeledStmt.class, new Builder()
//                .comment().property(ObservableProperty.LABEL).token(ASTParserConstants.COLON, ":").token(ASTParserConstants.EOF, " ").property(ObservableProperty.STATEMENT)
//                .build());
//
//        concreteSyntaxModelByClass.put(EmptyStmt.class, new Builder()
//                .comment().token(ASTParserConstants.SEMICOLON, ";")
//                .build());
//
//        concreteSyntaxModelByClass.put(ExpressionStmt.class, new Builder()
//                .orphanCommentsBeforeThis().comment().property(ObservableProperty.EXPRESSION).token(ASTParserConstants.SEMICOLON, ";")
//                .build());
//
//        concreteSyntaxModelByClass.put(SwitchStmt.class, new Builder()
//                .comment().token(ASTParserConstants.SWITCH, "switch").token(ASTParserConstants.LPAREN, "(").property(ObservableProperty.SELECTOR).token(ASTParserConstants.RPAREN, ")").token(ASTParserConstants.EOF, " ").token(ASTParserConstants.LBRACE, "{").newline()/* if (n.getEntries() != null) {
//    printer.indent();
//    for (final SwitchEntryStmt e : n.getEntries()) {
//        e.accept(this, arg);
//    }
//    printer.unindent();
//} */.token(ASTParserConstants.RBRACE, "}")
//                .build());
//
//        concreteSyntaxModelByClass.put(SwitchEntryStmt.class, new Builder()
//                .comment().conditional(ObservableProperty.LABEL, IS_PRESENT,.token(ASTParserConstants.CASE, "case").token(ASTParserConstants.EOF, " ").property(ObservableProperty.LABEL).token(ASTParserConstants.COLON, ":"),.token(ASTParserConstants._DEFAULT, "default").token(ASTParserConstants.COLON, ":")).
//        newline().indent()/* if (n.getStatements() != null) {
//    for (final Statement s : n.getStatements()) {
//        s.accept(this, arg);
//        printer.println();
//    }
//} */.unindent()
//                .build());
//
//        concreteSyntaxModelByClass.put(BreakStmt.class, new Builder()
//                .comment().token(ASTParserConstants.BREAK, "break")/* n.getLabel().ifPresent( l -> printer.print(" ").print(l.getIdentifier())); */.token(ASTParserConstants.SEMICOLON, ";")
//                .build());
//
//        concreteSyntaxModelByClass.put(ReturnStmt.class, new Builder()
//                .comment().token(ASTParserConstants.RETURN, "return").conditional(ObservableProperty.EXPRESSION, IS_PRESENT,.token(ASTParserConstants.EOF, " ").property(ObservableProperty.EXPRESSION), null).token(ASTParserConstants.SEMICOLON, ";")
//                .build());
//
//        concreteSyntaxModelByClass.put(EnumDeclaration.class, new Builder()
//                .comment().property(ObservableProperty.ANNOTATIONS).property(ObservableProperty.MODIFIERS).token(ASTParserConstants.ENUM, "enum").token(ASTParserConstants.EOF, " ").property(ObservableProperty.NAME).conditional(ObservableProperty.IMPLEMENTED_TYPES, IS_NOT_EMPTY,.token(ASTParserConstants.EOF, " ").token(ASTParserConstants.IMPLEMENTS, "implements").token(ASTParserConstants.EOF, " ")/* for (final Iterator<ClassOrInterfaceType> i = n.getImplementedTypes().iterator(); i.hasNext(); ) {
//    final ClassOrInterfaceType c = i.next();
//    c.accept(this, arg);
//    if (i.hasNext()) {
//        printer.print(", ");
//    }
//} */, null).token(ASTParserConstants.EOF, " ").token(ASTParserConstants.LBRACE, "{").newline().indent()/* if (n.getEntries() != null) {
//    printer.println();
//    for (final Iterator<EnumConstantDeclaration> i = n.getEntries().iterator(); i.hasNext(); ) {
//        final EnumConstantDeclaration e = i.next();
//        e.accept(this, arg);
//        if (i.hasNext()) {
//            printer.print(", ");
//        }
//    }
//} */.conditional(ObservableProperty.MEMBERS, IS_NOT_EMPTY,.token(ASTParserConstants.SEMICOLON, ";").newline().property(ObservableProperty.MEMBERS),.
//        conditional(ObservableProperty.ENTRIES, IS_NOT_EMPTY,.newline(), null)).
//        unindent().token(ASTParserConstants.RBRACE, "}")
//                .build());
//
//        concreteSyntaxModelByClass.put(EnumConstantDeclaration.class, new Builder()
//                .comment().property(ObservableProperty.ANNOTATIONS).property(ObservableProperty.NAME).conditional(ObservableProperty.ARGUMENTS, IS_NOT_EMPTY,.property(ObservableProperty.ARGUMENTS), null).conditional(ObservableProperty.CLASS_BODY, IS_NOT_EMPTY,.token(ASTParserConstants.EOF, " ").token(ASTParserConstants.LBRACE, "{").newline().indent().property(ObservableProperty.MEMBERS).unindent().token(ASTParserConstants.RBRACE, "}").newline(), null)
//.build());
//
//        concreteSyntaxModelByClass.put(EmptyMemberDeclaration.class, new Builder()
//                .comment().token(ASTParserConstants.SEMICOLON, ";")
//                .build());
//
//        concreteSyntaxModelByClass.put(InitializerDeclaration.class, new Builder()
//                .comment()/* if (n.isStatic()) {
//    printer.print("static ");
//} */.property(ObservableProperty.BODY)
//                .build());
//
//        concreteSyntaxModelByClass.put(IfStmt.class, new Builder()
//                .comment().token(ASTParserConstants.IF, "if").token(ASTParserConstants.EOF, " ").token(ASTParserConstants.LPAREN, "(").property(ObservableProperty.CONDITION)/* final boolean thenBlock = n.getThenStmt() instanceof BlockStmt; *//* if (// block statement should start on the same line
//thenBlock)
//    printer.print(") ");
//else {
//    printer.println(")");
//    printer.indent();
//} */.property(ObservableProperty.THEN_STMT)/* if (!thenBlock)
//    printer.unindent(); */.conditional(ObservableProperty.ELSE_STMT, IS_PRESENT,/* if (thenBlock)
//    printer.print(" ");
//else
//    printer.println(); *//* final boolean elseIf = n.getElseStmt().orElse(null) instanceof IfStmt; *//* final boolean elseBlock = n.getElseStmt().orElse(null) instanceof BlockStmt; *//* if (// put chained if and start of block statement on a same level
//elseIf || elseBlock)
//    printer.print("else ");
//else {
//    printer.println("else");
//    printer.indent();
//} */.conditional(ObservableProperty.ELSE_STMT, IS_PRESENT,.property(ObservableProperty.ELSE_STMT), null)/* if (!(elseIf || elseBlock))
//    printer.unindent(); */, null)
//.build());
//
//        concreteSyntaxModelByClass.put(WhileStmt.class, new Builder()
//                .comment().token(ASTParserConstants.WHILE, "while").token(ASTParserConstants.EOF, " ").token(ASTParserConstants.LPAREN, "(").property(ObservableProperty.CONDITION).token(ASTParserConstants.RPAREN, ")").token(ASTParserConstants.EOF, " ").property(ObservableProperty.BODY)
//                .build());
//
//        concreteSyntaxModelByClass.put(ContinueStmt.class, new Builder()
//                .comment().token(ASTParserConstants.CONTINUE, "continue")/* n.getLabel().ifPresent( l -> printer.print(" ").print(l.getIdentifier())); */.token(ASTParserConstants.SEMICOLON, ";")
//                .build());
//
//        concreteSyntaxModelByClass.put(DoStmt.class, new Builder()
//                .comment().token(ASTParserConstants.DO, "do").token(ASTParserConstants.EOF, " ").property(ObservableProperty.BODY).token(ASTParserConstants.EOF, " ").token(ASTParserConstants.WHILE, "while").token(ASTParserConstants.EOF, " ").token(ASTParserConstants.LPAREN, "(").property(ObservableProperty.CONDITION).token(ASTParserConstants.RPAREN, ")").token(ASTParserConstants.SEMICOLON, ";")
//                .build());
//
//        concreteSyntaxModelByClass.put(ForeachStmt.class, new Builder()
//                .comment().token(ASTParserConstants.FOR, "for").token(ASTParserConstants.EOF, " ").token(ASTParserConstants.LPAREN, "(").property(ObservableProperty.VARIABLE).token(ASTParserConstants.EOF, " ").token(ASTParserConstants.COLON, ":").token(ASTParserConstants.EOF, " ").property(ObservableProperty.ITERABLE).token(ASTParserConstants.RPAREN, ")").token(ASTParserConstants.EOF, " ").property(ObservableProperty.BODY)
//                .build());
//
//        concreteSyntaxModelByClass.put(ForStmt.class, new Builder()
//                .comment().token(ASTParserConstants.FOR, "for").token(ASTParserConstants.EOF, " ").token(ASTParserConstants.LPAREN, "(")/* if (n.getInitialization() != null) {
//    for (final Iterator<Expression> i = n.getInitialization().iterator(); i.hasNext(); ) {
//        final Expression e = i.next();
//        e.accept(this, arg);
//        if (i.hasNext()) {
//            printer.print(", ");
//        }
//    }
//} */.token(ASTParserConstants.SEMICOLON, ";").token(ASTParserConstants.EOF, " ").conditional(ObservableProperty.COMPARE, IS_PRESENT,.property(ObservableProperty.COMPARE), null).token(ASTParserConstants.SEMICOLON, ";").token(ASTParserConstants.EOF, " ")/* if (n.getUpdate() != null) {
//    for (final Iterator<Expression> i = n.getUpdate().iterator(); i.hasNext(); ) {
//        final Expression e = i.next();
//        e.accept(this, arg);
//        if (i.hasNext()) {
//            printer.print(", ");
//        }
//    }
//} */.token(ASTParserConstants.RPAREN, ")").token(ASTParserConstants.EOF, " ").property(ObservableProperty.BODY)
//                .build());
//
//        concreteSyntaxModelByClass.put(ThrowStmt.class, new Builder()
//                .comment().token(ASTParserConstants.THROW, "throw").token(ASTParserConstants.EOF, " ").property(ObservableProperty.EXPRESSION).token(ASTParserConstants.SEMICOLON, ";")
//                .build());
//
//        concreteSyntaxModelByClass.put(SynchronizedStmt.class, new Builder()
//                .comment().token(ASTParserConstants.SYNCHRONIZED, "synchronized").token(ASTParserConstants.EOF, " ").token(ASTParserConstants.LPAREN, "(").property(ObservableProperty.EXPRESSION).token(ASTParserConstants.RPAREN, ")").token(ASTParserConstants.EOF, " ").property(ObservableProperty.BODY)
//                .build());
//
//        concreteSyntaxModelByClass.put(TryStmt.class, new Builder()
//                .comment().token(ASTParserConstants.TRY, "try").token(ASTParserConstants.EOF, " ").conditional(ObservableProperty.RESOURCES, IS_NOT_EMPTY,.token(ASTParserConstants.LPAREN, "(")/* Iterator<VariableDeclarationExpr> resources = n.getResources().iterator(); *//* boolean first = true; *//* while (resources.hasNext()) {
//    visit(resources.next(), arg);
//    if (resources.hasNext()) {
//        printer.print(";");
//        printer.println();
//        if (first) {
//            printer.indent();
//        }
//    }
//    first = false;
//} *//* if (n.getResources().size() > 1) {
//    printer.unindent();
//} */.token(ASTParserConstants.RPAREN, ")").token(ASTParserConstants.EOF, " "), null).conditional(ObservableProperty.TRY_BLOCK, IS_PRESENT,.property(ObservableProperty.TRY_BLOCK), null)/* for (final CatchClause c : n.getCatchClauses()) {
//    c.accept(this, arg);
//} */.
//        conditional(ObservableProperty.FINALLY_BLOCK, IS_PRESENT,.token(ASTParserConstants.EOF, " ").token(ASTParserConstants.FINALLY, "finally").token(ASTParserConstants.EOF, " ").property(ObservableProperty.FINALLY_BLOCK), null)
//.build());
//
//        concreteSyntaxModelByClass.put(CatchClause.class, new Builder()
//                .comment().token(ASTParserConstants.EOF, " ").token(ASTParserConstants.CATCH, "catch").token(ASTParserConstants.EOF, " ").token(ASTParserConstants.LPAREN, "(").property(ObservableProperty.PARAMETER).token(ASTParserConstants.RPAREN, ")").token(ASTParserConstants.EOF, " ").property(ObservableProperty.BODY)
//                .build());
//
//        concreteSyntaxModelByClass.put(AnnotationDeclaration.class, new Builder()
//                .comment().property(ObservableProperty.ANNOTATIONS).property(ObservableProperty.MODIFIERS).token(ASTParserConstants.AT, "@").token(ASTParserConstants.INTERFACE, "interface").token(ASTParserConstants.EOF, " ").property(ObservableProperty.NAME).token(ASTParserConstants.EOF, " ").token(ASTParserConstants.LBRACE, "{").newline().indent()/* if (n.getMembers() != null) {
//    printMembers(n.getMembers(), arg);
//} */.unindent().token(ASTParserConstants.RBRACE, "}")
//                .build());
//
//        concreteSyntaxModelByClass.put(AnnotationMemberDeclaration.class, new Builder()
//                .comment().property(ObservableProperty.ANNOTATIONS).property(ObservableProperty.MODIFIERS).property(ObservableProperty.TYPE).token(ASTParserConstants.EOF, " ").property(ObservableProperty.NAME).token(ASTParserConstants.LPAREN, "(").token(ASTParserConstants.RPAREN, ")").conditional(ObservableProperty.DEFAULT_VALUE, IS_PRESENT,.token(ASTParserConstants.EOF, " ").token(ASTParserConstants._DEFAULT, "default").token(ASTParserConstants.EOF, " ").property(ObservableProperty.DEFAULT_VALUE), null).token(ASTParserConstants.SEMICOLON, ";")
//                .build());
//
//        concreteSyntaxModelByClass.put(MarkerAnnotationExpr.class, new Builder()
//                .comment().token(ASTParserConstants.AT, "@").property(ObservableProperty.NAME)
//                .build());
//
//        concreteSyntaxModelByClass.put(SingleMemberAnnotationExpr.class, new Builder()
//                .comment().token(ASTParserConstants.AT, "@").property(ObservableProperty.NAME).token(ASTParserConstants.LPAREN, "(").property(ObservableProperty.MEMBER_VALUE).token(ASTParserConstants.RPAREN, ")")
//                .build());
//
//        concreteSyntaxModelByClass.put(NormalAnnotationExpr.class, new Builder()
//                .comment().token(ASTParserConstants.AT, "@").property(ObservableProperty.NAME).token(ASTParserConstants.LPAREN, "(")/* if (n.getPairs() != null) {
//    for (final Iterator<MemberValuePair> i = n.getPairs().iterator(); i.hasNext(); ) {
//        final MemberValuePair m = i.next();
//        m.accept(this, arg);
//        if (i.hasNext()) {
//            printer.print(", ");
//        }
//    }
//} */.token(ASTParserConstants.RPAREN, ")")
//                .build());
//
//        concreteSyntaxModelByClass.put(MemberValuePair.class, new Builder()
//                .comment().property(ObservableProperty.NAME).token(ASTParserConstants.EOF, " ").token(ASTParserConstants.ASSIGN, "=").token(ASTParserConstants.EOF, " ").property(ObservableProperty.VALUE)
//                .build());
//
//        concreteSyntaxModelByClass.put(LineComment.class, new Builder()
///* if (!configuration.isPrintComments()) {
//    return;
//} */.token(ASTParserConstants.SLASH, "/").token(ASTParserConstants.SLASH, "/")/* String tmp = n.getContent(); *//* tmp = tmp.replace('\r', ' '); *//* tmp = tmp.replace('\n', ' '); *//* printer.println(tmp); */
//                .build());
//
//        concreteSyntaxModelByClass.put(BlockComment.class, new Builder()
///* if (!configuration.isPrintComments()) {
//    return;
//} */.token(ASTParserConstants.JAVA_DOC_COMMENT, "*/").newline()
//                .build());
//
//        concreteSyntaxModelByClass.put(LambdaExpr.class, new Builder()
//                .comment()/* final NodeList<Parameter> parameters = n.getParameters(); *//* final boolean printPar = n.isEnclosingParameters(); *//* if (printPar) {
//    printer.print("(");
//} *//* for (Iterator<Parameter> i = parameters.iterator(); i.hasNext(); ) {
//    Parameter p = i.next();
//    p.accept(this, arg);
//    if (i.hasNext()) {
//        printer.print(", ");
//    }
//} *//* if (printPar) {
//    printer.print(")");
//} */.token(ASTParserConstants.EOF, " ").token(ASTParserConstants.ARROW, "->").token(ASTParserConstants.EOF, " ")/* final Statement body = n.getBody(); *//* if (body instanceof ExpressionStmt) {
//    // Print the expression directly
//    ((ExpressionStmt) body).getExpression().accept(this, arg);
//} else {
//    body.accept(this, arg);
//} */
//                .build());
//
//        concreteSyntaxModelByClass.put(MethodReferenceExpr.class, new Builder()
//                .comment()/* Expression scope = n.getScope(); *//* String identifier = n.getIdentifier(); *//* if (scope != null) {
//    n.getScope().accept(this, arg);
//} */.token(ASTParserConstants.DOUBLECOLON, "::").property(ObservableProperty.TYPE_ARGUMENTS)/* if (identifier != null) {
//    printer.print(identifier);
//} */
//                .build());
//
//        concreteSyntaxModelByClass.put(TypeExpr.class, new Builder()
//                .comment()/* if (n.getType() != null) {
//    n.getType().accept(this, arg);
//} */
//                .build());
//
//        concreteSyntaxModelByClass.put(NodeList.class, new Builder()
///* for (Object node : n) {
//    ((Node) node).accept(this, arg);
//} */
//                .build());
//
//        concreteSyntaxModelByClass.put(ImportDeclaration.class, new Builder()
//                .comment().token(ASTParserConstants.IMPORT, "import").token(ASTParserConstants.EOF, " ")/* if (n.isStatic()) {
//    printer.print("static ");
//} */.property(ObservableProperty.NAME)/* if (n.isAsterisk()) {
//    printer.print(".*");
//} */.token(ASTParserConstants.SEMICOLON, ";").newline().orphanCommentsEnding()
//                .build());

    }

    public CsmElement getTopElement() {
        throw new UnsupportedOperationException();
    }

    private ConcreteSyntaxModel() {

    }

    public void prettyPrint(Node node, SourcePrinter printer) {
        elements.forEach(e -> e.prettyPrint(node, printer));
    }

    private static class Builder {
        List<CsmElement> elements = new LinkedList<>();

        Builder add(CsmElement e) {
            elements.add(e);
            return this;
        }

        Builder comment() {
            return add(new CsmComment());
        }

        Builder child(ObservableProperty property) {
            return add(new CsmChild(property));
        }

        Builder property(ObservableProperty property) {
            return add(new CsmChild(property));
        }

        Builder value(ObservableProperty property) {
            return add(new CsmAttribute(property));
        }

        Builder string(int tokenType, String content) {
            return add(new CsmToken(tokenType, content));
        }

        Builder token(int tokenType, String content) {
            return add(new CsmToken(tokenType, content));
        }

        Builder space() {
            return add(ConcreteSyntaxModel.space());
        }

        Builder newline() {
            return add(ConcreteSyntaxModel.newline());
        }

        Builder semicolon() {
            return add(ConcreteSyntaxModel.semicolon());
        }

        Builder string(int tokenType) {
            return add(new CsmToken(tokenType));
        }

        Builder string(int tokenType, ObservableProperty content) {
            return add(new CsmToken(tokenType, content));
        }

        Builder ifThen(ObservableProperty childCondition, Element thenElement) {
            return add(new CsmConditional(childCondition, thenElement));
        }

        Builder ifThenElse(ObservableProperty childCondition, Element thenElement, Element elseElement) {
            return add(new CsmConditional(childCondition, thenElement, elseElement));
        }

        Builder ifThenElse(Predicate<Node> predicate, Element thenElement, Element elseElement) {
            return add(new CsmConditional(predicate, thenElement, elseElement));
        }

        Builder sequence(Element... elements) {
            return add(new CsmSequence(Arrays.asList(elements)));
        }

        Builder list(ObservableProperty listProperty, Element following) {
            return add(new CsmList(listProperty, following));
        }

        Builder list(ObservableProperty listProperty) {
            return add(new CsmList(listProperty));
        }

        Builder list(ObservableProperty property, Element separator, Element preceeding, Element following) {
            return add(new CsmList(property, separator, preceeding, following));
        }

        ConcreteSyntaxModel build() {
            ConcreteSyntaxModel instance = new ConcreteSyntaxModel();
            instance.elements = this.elements;
            return instance;
        }

        Builder indent() {
            return add(new CsmIndent());
        }

        Builder unindent() {
            return add(new CsmUnindent());
        }

        Builder orphanCommentsBeforeThis() {
            //throw new UnsupportedOperationException();
            return this;
        }

        Builder annotations() {
            return add(ConcreteSyntaxModel.list(ObservableProperty.ANNOTATIONS, ConcreteSyntaxModel.newline(), null, ConcreteSyntaxModel.newline()));
        }

        Builder modifiers() {
            return list(ObservableProperty.MODIFIERS, null, ConcreteSyntaxModel.space(), ConcreteSyntaxModel.space());
        }

        public Builder orphanCommentsEnding() {
            return add((node, printer) -> {
                List<Node> everything = new LinkedList<>();
                everything.addAll(node.getChildNodes());
                sortByBeginPosition(everything);
                if (everything.isEmpty()) {
                    return;
                }

                int commentsAtEnd = 0;
                boolean findingComments = true;
                while (findingComments && commentsAtEnd < everything.size()) {
                    Node last = everything.get(everything.size() - 1 - commentsAtEnd);
                    findingComments = (last instanceof Comment);
                    if (findingComments) {
                        commentsAtEnd++;
                    }
                }
                for (int i = 0; i < commentsAtEnd; i++) {
                    genericPrettyPrint(everything.get(everything.size() - commentsAtEnd + i));
                }
            });
        }

        public Builder block(Element element) {
            add(ConcreteSyntaxModel.string(ASTParserConstants.LBRACE));
            add(ConcreteSyntaxModel.newline());
            indent();
            add(element);
            unindent();
            return add(ConcreteSyntaxModel.string(ASTParserConstants.RBRACE));
        }
    }

    public static void genericPrettyPrint(Node node, SourcePrinter printer) {
        forClass(node.getClass()).prettyPrint(node, printer);
    }

    public static String genericPrettyPrint(Node node) {
        SourcePrinter sourcePrinter = new SourcePrinter("    ");
        forClass(node.getClass()).prettyPrint(node, sourcePrinter);
        return sourcePrinter.getSource();
    }

    private static CsmSequence sequence(Element... elements) {
        return new CsmSequence(Arrays.asList(elements));
    }

    private static CsmChild child(ObservableProperty property) {
        return new CsmChild(property);
    }

    private static Element child(Node child) {
        return (node, printer) -> genericPrettyPrint(child, printer);
    }

    private static CsmList list(ObservableProperty property) {
        return new CsmList(property);
    }

    private static CsmList list(ObservableProperty property, Element separator, Element preceeding, Element following) {
        return new CsmList(property, separator, preceeding, following);
    }

    private static CsmToken string(int tokenType, String content) {
        return new CsmToken(tokenType, content);
    }

    private static CsmToken string(int tokenType) {
        return new CsmToken(tokenType);
    }

    private static CsmToken space() {
        return new CsmToken(32, " ");
    }

    private static CsmToken semicolon() {
        return new CsmToken(ASTParserConstants.SEMICOLON);
    }

    private static CsmToken newline() {
        return new CsmToken(3, "\n");
    }

    private static CsmToken comma() {
        return new CsmToken(ASTParserConstants.COMMA);
    }


    public static ConcreteSyntaxModel forClass(Class<? extends Node> nodeClazz) {
        if (!concreteSyntaxModelByClass.containsKey(nodeClazz)) {
            throw new UnsupportedOperationException(nodeClazz.getSimpleName());
        }
        return concreteSyntaxModelByClass.get(nodeClazz);
    }

}
