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

import com.github.javaparser.GeneratedJavaParserConstants;
import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.modules.*;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.printer.concretesyntaxmodel.CsmConditional;
import com.github.javaparser.printer.concretesyntaxmodel.CsmElement;
import com.github.javaparser.printer.concretesyntaxmodel.CsmMix;

import java.util.*;
import java.util.stream.Collectors;

import static com.github.javaparser.GeneratedJavaParserConstants.*;
import static com.github.javaparser.ast.observer.ObservableProperty.*;
import static com.github.javaparser.printer.concretesyntaxmodel.CsmConditional.Condition.*;
import static com.github.javaparser.printer.concretesyntaxmodel.CsmElement.*;

/**
 * The Concrete Syntax Model for a single node type. It knows the syntax used to represent a certain element in Java
 * code.
 */
public class ConcreteSyntaxModel {

    private static final Map<Class, CsmElement> concreteSyntaxModelByClass = new HashMap<>();
    private static Optional<String> initializationError;

    private static CsmElement modifiers() {
        return list(ObservableProperty.MODIFIERS, space(), none(), space());
    }

    /**
     * Build a mix collecting all the elements specified.
     */
    private static CsmElement mix(CsmElement... elements) {
        return new CsmMix(Arrays.asList(elements));
    }

    private static CsmElement memberAnnotations() {
        return list(ObservableProperty.ANNOTATIONS, newline(), none(), newline());
    }

    private static CsmElement annotations() {
        return list(ObservableProperty.ANNOTATIONS, space(), none(), newline());
    }

    private static CsmElement typeParameters() {
        return list(ObservableProperty.TYPE_PARAMETERS, sequence(comma(), space()), token(GeneratedJavaParserConstants.LT),
                sequence(token(GeneratedJavaParserConstants.GT), space()));
    }

    private static CsmElement typeArguments() {
        return list(ObservableProperty.TYPE_ARGUMENTS, sequence(comma(), space()), token(GeneratedJavaParserConstants.LT),
                sequence(token(GeneratedJavaParserConstants.GT)));
    }

    static {

        ///
        /// Body
        ///

        concreteSyntaxModelByClass.put(AnnotationDeclaration.class, sequence(
                comment(),
                memberAnnotations(),
                modifiers(),
                token(GeneratedJavaParserConstants.AT),
                token(GeneratedJavaParserConstants.INTERFACE),
                space(),
                child(ObservableProperty.NAME),
                space(),
                token(LBRACE),
                newline(),
                indent(),
                list(ObservableProperty.MEMBERS, newline(), none(), none(), newline()),
                unindent(),
                token(RBRACE)
        ));

        concreteSyntaxModelByClass.put(AnnotationMemberDeclaration.class, sequence(
                comment(),
                memberAnnotations(),
                modifiers(),
                child(ObservableProperty.TYPE),
                space(),
                child(ObservableProperty.NAME),
                token(LPAREN),
                token(RPAREN),
                conditional(ObservableProperty.DEFAULT_VALUE, IS_PRESENT, sequence(space(), token(GeneratedJavaParserConstants._DEFAULT), space(), child(DEFAULT_VALUE))),
                semicolon()
        ));

        concreteSyntaxModelByClass.put(ClassOrInterfaceDeclaration.class, sequence(
                comment(),
                memberAnnotations(),
                modifiers(),
                conditional(ObservableProperty.INTERFACE, FLAG, token(GeneratedJavaParserConstants.INTERFACE), token(GeneratedJavaParserConstants.CLASS)),
                space(),
                child(ObservableProperty.NAME),
                list(TYPE_PARAMETERS, sequence(comma(), space()), string(GeneratedJavaParserConstants.LT), string(GeneratedJavaParserConstants.GT)),
                list(ObservableProperty.EXTENDED_TYPES,
                        sequence(string(GeneratedJavaParserConstants.COMMA), space()),
                        sequence(space(), token(GeneratedJavaParserConstants.EXTENDS), space()),
                        none()),
                list(ObservableProperty.IMPLEMENTED_TYPES, sequence(string(GeneratedJavaParserConstants.COMMA), space()), sequence(
                        space(),
                        token(GeneratedJavaParserConstants.IMPLEMENTS),
                        space()), none()),
                space(),
                block(sequence(newline(), list(ObservableProperty.MEMBERS, sequence(newline(), newline()), newline(), newline())))
        ));

        concreteSyntaxModelByClass.put(ConstructorDeclaration.class, sequence(
                comment(),
                memberAnnotations(),
                modifiers(),
                typeParameters(),
                child(ObservableProperty.NAME),
                token(GeneratedJavaParserConstants.LPAREN),
                list(ObservableProperty.PARAMETERS, sequence(comma(), space()), none(), none()),
                token(GeneratedJavaParserConstants.RPAREN),
                list(ObservableProperty.THROWN_EXCEPTIONS, sequence(comma(), space()), sequence(space(), token(GeneratedJavaParserConstants.THROWS), space()), none()),
                space(),
                child(ObservableProperty.BODY)
        ));

        concreteSyntaxModelByClass.put(EnumConstantDeclaration.class, sequence(
                comment(),
                memberAnnotations(),
                child(ObservableProperty.NAME),
                list(ObservableProperty.ARGUMENTS, sequence(comma(), space()), token(GeneratedJavaParserConstants.LPAREN), token(GeneratedJavaParserConstants.RPAREN)),
                conditional(CLASS_BODY, IS_NOT_EMPTY, sequence(space(), token(GeneratedJavaParserConstants.LBRACE), newline(), indent(), newline(),
                        list(ObservableProperty.CLASS_BODY, newline(), newline(), none(), newline()),
                        unindent(),
                        token(RBRACE), newline()))
        ));

        concreteSyntaxModelByClass.put(EnumDeclaration.class, sequence(
                comment(),
                annotations(),
                modifiers(),
                token(GeneratedJavaParserConstants.ENUM),
                space(),
                child(ObservableProperty.NAME),
                list(ObservableProperty.IMPLEMENTED_TYPES,
                        sequence(comma(), space()),
                        sequence(space(), token(GeneratedJavaParserConstants.IMPLEMENTS), space()),
                        none()),
                space(),
                token(GeneratedJavaParserConstants.LBRACE),
                newline(),
                indent(),
                newline(),
                list(ObservableProperty.ENTRIES,
                        sequence(comma(), newline()),
                        none(),
                        none()),
                conditional(ObservableProperty.MEMBERS, IS_EMPTY,
                        conditional(ObservableProperty.ENTRIES, IS_NOT_EMPTY, newline()),
                        sequence(semicolon(), newline(), newline(), list(ObservableProperty.MEMBERS, newline(), newline(), none(), newline()))),
                unindent(),
                token(RBRACE)
        ));

        concreteSyntaxModelByClass.put(FieldDeclaration.class, sequence(
                orphanCommentsBeforeThis(),
                comment(),
                annotations(),
                modifiers(),
                conditional(ObservableProperty.VARIABLES, IS_NOT_EMPTY, child(ObservableProperty.MAXIMUM_COMMON_TYPE)),
                space(),
                list(ObservableProperty.VARIABLES, sequence(comma(), space())),
                semicolon()));

        concreteSyntaxModelByClass.put(InitializerDeclaration.class, sequence(
                comment(),
                conditional(ObservableProperty.STATIC, FLAG, sequence(token(GeneratedJavaParserConstants.STATIC), space())),
                child(ObservableProperty.BODY)));

        concreteSyntaxModelByClass.put(MethodDeclaration.class, sequence(
                orphanCommentsBeforeThis(),
                comment(),
                mix(memberAnnotations(), modifiers()),
                typeParameters(),
                child(ObservableProperty.TYPE),
                space(),
                child(ObservableProperty.NAME),
                token(GeneratedJavaParserConstants.LPAREN),
                conditional(ObservableProperty.RECEIVER_PARAMETER, IS_PRESENT, sequence(child(ObservableProperty.RECEIVER_PARAMETER), comma(), space())),
                list(ObservableProperty.PARAMETERS, sequence(comma(), space()), none(), none()),
                token(GeneratedJavaParserConstants.RPAREN),
                list(ObservableProperty.THROWN_EXCEPTIONS, sequence(comma(), space()), sequence(space(), token(GeneratedJavaParserConstants.THROWS), space()), none()),
                conditional(ObservableProperty.BODY, IS_PRESENT, sequence(space(), child(ObservableProperty.BODY)), semicolon())
        ));

        concreteSyntaxModelByClass.put(Parameter.class, sequence(
                comment(),
                list(ObservableProperty.ANNOTATIONS, space(), none(), space()),
                modifiers(),
                child(ObservableProperty.TYPE),
                conditional(ObservableProperty.VAR_ARGS, FLAG, sequence(
                        list(ObservableProperty.VAR_ARGS_ANNOTATIONS, space(), none(), none()),
                        token(GeneratedJavaParserConstants.ELLIPSIS))),
                space(),
                child(ObservableProperty.NAME)));

        concreteSyntaxModelByClass.put(ReceiverParameter.class, sequence(
                comment(),
                list(ObservableProperty.ANNOTATIONS, space(), none(), space()),
                child(ObservableProperty.TYPE),
                space(),
                child(ObservableProperty.NAME)));

        concreteSyntaxModelByClass.put(VariableDeclarator.class, sequence(
                comment(),
                child(ObservableProperty.NAME),
                // FIXME: we should introduce a derived property
                // list(ObservableProperty.EXTRA_ARRAY_LEVELS),
                conditional(ObservableProperty.INITIALIZER, IS_PRESENT, sequence(space(), token(GeneratedJavaParserConstants.ASSIGN), space(),
                        child(ObservableProperty.INITIALIZER)))
        ));

        ///
        /// Expressions
        ///

        concreteSyntaxModelByClass.put(ArrayAccessExpr.class, sequence(
                comment(),
                child(ObservableProperty.NAME),
                token(GeneratedJavaParserConstants.LBRACKET),
                child(ObservableProperty.INDEX),
                token(GeneratedJavaParserConstants.RBRACKET)
        ));

        concreteSyntaxModelByClass.put(ArrayCreationExpr.class, sequence(
                comment(),
                token(GeneratedJavaParserConstants.NEW),
                space(),
                child(ObservableProperty.ELEMENT_TYPE),
                list(ObservableProperty.LEVELS),
                conditional(ObservableProperty.INITIALIZER, IS_PRESENT, sequence(space(), child(ObservableProperty.INITIALIZER)))
        ));

        concreteSyntaxModelByClass.put(ArrayInitializerExpr.class, sequence(
                comment(),
                token(GeneratedJavaParserConstants.LBRACE),
                list(ObservableProperty.VALUES, sequence(comma(), space()), space(), space()),
                orphanCommentsEnding(),
                token(RBRACE)));

        concreteSyntaxModelByClass.put(AssignExpr.class, sequence(
                comment(),
                child(ObservableProperty.TARGET),
                space(),
                attribute(ObservableProperty.OPERATOR),
                space(),
                child(ObservableProperty.VALUE)
        ));

        concreteSyntaxModelByClass.put(BinaryExpr.class, sequence(
                comment(),
                child(ObservableProperty.LEFT),
                space(),
                attribute(ObservableProperty.OPERATOR),
                space(),
                child(ObservableProperty.RIGHT)
        ));

        concreteSyntaxModelByClass.put(BooleanLiteralExpr.class, sequence(
                comment(), attribute(VALUE)
        ));

        concreteSyntaxModelByClass.put(CastExpr.class, sequence(
                comment(),
                token(GeneratedJavaParserConstants.LPAREN),
                child(ObservableProperty.TYPE),
                token(GeneratedJavaParserConstants.RPAREN),
                space(),
                child(ObservableProperty.EXPRESSION)
        ));

        concreteSyntaxModelByClass.put(CharLiteralExpr.class, sequence(
                comment(),
                charToken(ObservableProperty.VALUE)
        ));

        concreteSyntaxModelByClass.put(ClassExpr.class, sequence(
                comment(), child(ObservableProperty.TYPE), token(GeneratedJavaParserConstants.DOT), token(GeneratedJavaParserConstants.CLASS)));

        concreteSyntaxModelByClass.put(ConditionalExpr.class, sequence(
                comment(),
                child(ObservableProperty.CONDITION),
                space(),
                token(GeneratedJavaParserConstants.HOOK),
                space(),
                child(ObservableProperty.THEN_EXPR),
                space(),
                token(GeneratedJavaParserConstants.COLON),
                space(),
                child(ObservableProperty.ELSE_EXPR)
        ));

        concreteSyntaxModelByClass.put(DoubleLiteralExpr.class, sequence(
                comment(),
                attribute(ObservableProperty.VALUE)
        ));

        concreteSyntaxModelByClass.put(EnclosedExpr.class, sequence(
                comment(),
                token(GeneratedJavaParserConstants.LPAREN),
                child(ObservableProperty.INNER),
                token(GeneratedJavaParserConstants.RPAREN)
        ));

        concreteSyntaxModelByClass.put(FieldAccessExpr.class, sequence(
                comment(),
                child(SCOPE),
                token(GeneratedJavaParserConstants.DOT),
                child(ObservableProperty.NAME)
        ));

        concreteSyntaxModelByClass.put(InstanceOfExpr.class, sequence(
                comment(),
                child(ObservableProperty.EXPRESSION),
                space(),
                token(GeneratedJavaParserConstants.INSTANCEOF),
                space(),
                child(ObservableProperty.TYPE)
        ));

        concreteSyntaxModelByClass.put(IntegerLiteralExpr.class, sequence(
                comment(),
                attribute(ObservableProperty.VALUE)
        ));

        concreteSyntaxModelByClass.put(LambdaExpr.class, sequence(
                comment(),
                conditional(ObservableProperty.ENCLOSING_PARAMETERS, FLAG, token(GeneratedJavaParserConstants.LPAREN)),
                list(ObservableProperty.PARAMETERS, sequence(comma(), space())),
                conditional(ObservableProperty.ENCLOSING_PARAMETERS, FLAG, token(GeneratedJavaParserConstants.RPAREN)),
                space(),
                token(GeneratedJavaParserConstants.ARROW),
                space(),
                conditional(ObservableProperty.EXPRESSION_BODY, IS_PRESENT, child(ObservableProperty.EXPRESSION_BODY), child(ObservableProperty.BODY))
        ));

        concreteSyntaxModelByClass.put(LongLiteralExpr.class, sequence(
                comment(),
                attribute(ObservableProperty.VALUE)
        ));

        concreteSyntaxModelByClass.put(MarkerAnnotationExpr.class, sequence(comment(), token(GeneratedJavaParserConstants.AT), attribute(ObservableProperty.NAME)));

        concreteSyntaxModelByClass.put(MemberValuePair.class, sequence(comment(),
                child(ObservableProperty.NAME),
                space(),
                token(GeneratedJavaParserConstants.ASSIGN),
                space(),
                child(ObservableProperty.VALUE)));

        concreteSyntaxModelByClass.put(MethodCallExpr.class, sequence(
                comment(),
                conditional(ObservableProperty.SCOPE, IS_PRESENT, sequence(child(ObservableProperty.SCOPE), token(GeneratedJavaParserConstants.DOT))),
                typeArguments(),
                child(ObservableProperty.NAME),
                token(GeneratedJavaParserConstants.LPAREN),
                list(ObservableProperty.ARGUMENTS, sequence(comma(), space()), none(), none()),
                token(GeneratedJavaParserConstants.RPAREN)
        ));

        concreteSyntaxModelByClass.put(MethodReferenceExpr.class, sequence(
                comment(),
                child(ObservableProperty.SCOPE),
                token(GeneratedJavaParserConstants.DOUBLECOLON),
                typeArguments(),
                attribute(ObservableProperty.IDENTIFIER)
        ));

        concreteSyntaxModelByClass.put(Modifier.class, attribute(ObservableProperty.KEYWORD));

        concreteSyntaxModelByClass.put(Name.class, sequence(
                comment(),
                conditional(ObservableProperty.QUALIFIER, IS_PRESENT, sequence(child(ObservableProperty.QUALIFIER), token(GeneratedJavaParserConstants.DOT))),
                attribute(ObservableProperty.IDENTIFIER),
                orphanCommentsEnding()
        ));

        concreteSyntaxModelByClass.put(NameExpr.class, sequence(
                comment(),
                child(ObservableProperty.NAME),
                orphanCommentsEnding()
        ));

        concreteSyntaxModelByClass.put(NormalAnnotationExpr.class, sequence(
                comment(),
                token(GeneratedJavaParserConstants.AT),
                child(ObservableProperty.NAME),
                token(GeneratedJavaParserConstants.LPAREN),
                list(ObservableProperty.PAIRS, sequence(comma(), space())),
                token(GeneratedJavaParserConstants.RPAREN)
        ));

        concreteSyntaxModelByClass.put(NullLiteralExpr.class, sequence(
                comment(),
                token(GeneratedJavaParserConstants.NULL)
        ));

        concreteSyntaxModelByClass.put(ObjectCreationExpr.class, sequence(
                comment(),
                conditional(ObservableProperty.SCOPE, IS_PRESENT, sequence(child(ObservableProperty.SCOPE), token(GeneratedJavaParserConstants.DOT))),
                token(GeneratedJavaParserConstants.NEW),
                space(),
                list(ObservableProperty.TYPE_ARGUMENTS, sequence(comma(), space()), token(LT), token(GT)),
                conditional(ObservableProperty.TYPE_ARGUMENTS, IS_NOT_EMPTY, space()),
                child(ObservableProperty.TYPE),
                token(GeneratedJavaParserConstants.LPAREN),
                list(ObservableProperty.ARGUMENTS, sequence(comma(), space()), none(), none()),
                token(GeneratedJavaParserConstants.RPAREN),
                conditional(ObservableProperty.ANONYMOUS_CLASS_BODY, IS_PRESENT,
                        sequence(
                                space(), token(LBRACE), newline(), indent(),
                                list(ObservableProperty.ANONYMOUS_CLASS_BODY,
                                        newline(),
                                        newline(),
                                        newline(),
                                        newline()),
                                unindent(),
                                token(RBRACE)
                        ))
        ));

        concreteSyntaxModelByClass.put(SimpleName.class, attribute(ObservableProperty.IDENTIFIER));

        concreteSyntaxModelByClass.put(SingleMemberAnnotationExpr.class, sequence(
                comment(),
                token(GeneratedJavaParserConstants.AT),
                child(ObservableProperty.NAME),
                token(GeneratedJavaParserConstants.LPAREN),
                child(ObservableProperty.MEMBER_VALUE),
                token(GeneratedJavaParserConstants.RPAREN)));

        concreteSyntaxModelByClass.put(StringLiteralExpr.class, sequence(
                comment(),
                stringToken(ObservableProperty.VALUE)
        ));

        concreteSyntaxModelByClass.put(SuperExpr.class, sequence(
                comment(),
                conditional(TYPE_NAME, IS_PRESENT, sequence(child(TYPE_NAME), token(GeneratedJavaParserConstants.DOT))),
                token(GeneratedJavaParserConstants.SUPER)
        ));

        concreteSyntaxModelByClass.put(ThisExpr.class, sequence(
                comment(),
                conditional(TYPE_NAME, IS_PRESENT, sequence(child(TYPE_NAME), token(GeneratedJavaParserConstants.DOT))),
                token(GeneratedJavaParserConstants.THIS)
        ));

        concreteSyntaxModelByClass.put(TypeExpr.class, sequence(
                comment(),
                child(ObservableProperty.TYPE)
        ));

        concreteSyntaxModelByClass.put(UnaryExpr.class, sequence(
                conditional(ObservableProperty.PREFIX, FLAG, attribute(ObservableProperty.OPERATOR)),
                child(ObservableProperty.EXPRESSION),
                conditional(ObservableProperty.POSTFIX, FLAG, attribute(ObservableProperty.OPERATOR))
        ));

        concreteSyntaxModelByClass.put(VariableDeclarationExpr.class, sequence(
                comment(),
                list(ObservableProperty.ANNOTATIONS, space(), none(), space()),
                modifiers(),
                child(ObservableProperty.MAXIMUM_COMMON_TYPE),
                space(),
                list(ObservableProperty.VARIABLES, sequence(comma(), space()))
        ));

        ///
        /// Statements
        ///

        concreteSyntaxModelByClass.put(AssertStmt.class, sequence(
                comment(),
                token(GeneratedJavaParserConstants.ASSERT),
                space(),
                child(ObservableProperty.CHECK),
                conditional(ObservableProperty.MESSAGE, IS_PRESENT, sequence(
                        space(),
                        token(GeneratedJavaParserConstants.COLON),
                        space(),
                        child(ObservableProperty.MESSAGE)
                )),
                semicolon()
        ));

        concreteSyntaxModelByClass.put(BlockStmt.class, sequence(
                orphanCommentsBeforeThis(),
                comment(),
                token(GeneratedJavaParserConstants.LBRACE),
                newline(),
                list(ObservableProperty.STATEMENTS, newline(), indent(), sequence(newline(), unindent())),
                orphanCommentsEnding(),
                token(RBRACE)
        ));

        concreteSyntaxModelByClass.put(BreakStmt.class, sequence(
                comment(),
                token(GeneratedJavaParserConstants.BREAK),
                conditional(VALUE, IS_PRESENT, sequence(space(), child(VALUE))),
                semicolon()
        ));

        concreteSyntaxModelByClass.put(CatchClause.class, sequence(
                comment(),
                space(),
                token(GeneratedJavaParserConstants.CATCH),
                space(),
                token(LPAREN),
                child(ObservableProperty.PARAMETER),
                token(RPAREN),
                space(),
                child(BODY)
        ));

        concreteSyntaxModelByClass.put(ContinueStmt.class, sequence(
                comment(),
                token(GeneratedJavaParserConstants.CONTINUE),
                conditional(ObservableProperty.LABEL, IS_PRESENT, sequence(space(), child(ObservableProperty.LABEL))),
                semicolon()
        ));

        concreteSyntaxModelByClass.put(DoStmt.class, sequence(
                comment(),
                token(GeneratedJavaParserConstants.DO),
                space(),
                child(ObservableProperty.BODY),
                space(),
                token(GeneratedJavaParserConstants.WHILE),
                space(),
                token(GeneratedJavaParserConstants.LPAREN),
                child(ObservableProperty.CONDITION),
                token(GeneratedJavaParserConstants.RPAREN),
                semicolon()
        ));

        concreteSyntaxModelByClass.put(EmptyStmt.class, sequence(
                comment(),
                token(GeneratedJavaParserConstants.SEMICOLON)
        ));

        concreteSyntaxModelByClass.put(UnparsableStmt.class, sequence(
                comment(),
                token(GeneratedJavaParserConstants.SEMICOLON)
        ));

        concreteSyntaxModelByClass.put(ExplicitConstructorInvocationStmt.class, sequence(
                comment(),
                conditional(ObservableProperty.THIS, FLAG,
                        sequence(typeArguments(), token(GeneratedJavaParserConstants.THIS)),
                        sequence(
                                conditional(ObservableProperty.EXPRESSION, IS_PRESENT, sequence(child(ObservableProperty.EXPRESSION), token(GeneratedJavaParserConstants.DOT))),
                                typeArguments(),
                                token(GeneratedJavaParserConstants.SUPER)
                        )),
                token(GeneratedJavaParserConstants.LPAREN),
                list(ObservableProperty.ARGUMENTS, sequence(comma(), space())),
                token(GeneratedJavaParserConstants.RPAREN),
                semicolon()
        ));

        concreteSyntaxModelByClass.put(ExpressionStmt.class, sequence(
                orphanCommentsBeforeThis(),
                comment(),
                child(ObservableProperty.EXPRESSION),
                semicolon()
        ));

        concreteSyntaxModelByClass.put(ForEachStmt.class, sequence(
                comment(),
                token(GeneratedJavaParserConstants.FOR),
                space(),
                token(GeneratedJavaParserConstants.LPAREN),
                child(ObservableProperty.VARIABLE),
                space(),
                token(GeneratedJavaParserConstants.COLON),
                space(),
                child(ObservableProperty.ITERABLE),
                token(GeneratedJavaParserConstants.RPAREN),
                space(),
                child(ObservableProperty.BODY)
        ));

        concreteSyntaxModelByClass.put(ForStmt.class, sequence(
                comment(),
                token(GeneratedJavaParserConstants.FOR),
                space(),
                token(GeneratedJavaParserConstants.LPAREN),
                list(ObservableProperty.INITIALIZATION, sequence(comma(), space())),
                semicolon(),
                space(),
                child(ObservableProperty.COMPARE),
                semicolon(),
                space(),
                list(ObservableProperty.UPDATE, sequence(comma(), space())),
                token(GeneratedJavaParserConstants.RPAREN),
                space(),
                child(ObservableProperty.BODY)
        ));

        concreteSyntaxModelByClass.put(IfStmt.class, sequence(
                comment(),
                token(GeneratedJavaParserConstants.IF),
                space(),
                token(GeneratedJavaParserConstants.LPAREN),
                child(ObservableProperty.CONDITION),
                token(GeneratedJavaParserConstants.RPAREN),
                conditional(ObservableProperty.THEN_BLOCK, CsmConditional.Condition.FLAG,
                        sequence(space(), child(ObservableProperty.THEN_STMT),
                                conditional(ObservableProperty.ELSE_STMT, IS_PRESENT, space())),
                        sequence(newline(), indent(), child(ObservableProperty.THEN_STMT),
                                conditional(ObservableProperty.ELSE_STMT, IS_PRESENT, newline()),
                                unindent())),
                conditional(ObservableProperty.ELSE_STMT, IS_PRESENT,
                        sequence(token(GeneratedJavaParserConstants.ELSE),
                                conditional(Arrays.asList(ObservableProperty.ELSE_BLOCK, ObservableProperty.CASCADING_IF_STMT), CsmConditional.Condition.FLAG,
                                        sequence(space(), child(ObservableProperty.ELSE_STMT)),
                                        sequence(newline(), indent(), child(ObservableProperty.ELSE_STMT), unindent()))))
        ));

        concreteSyntaxModelByClass.put(LabeledStmt.class, sequence(
                comment(),
                child(ObservableProperty.LABEL),
                token(GeneratedJavaParserConstants.COLON),
                space(),
                child(ObservableProperty.STATEMENT)
        ));

        concreteSyntaxModelByClass.put(LocalClassDeclarationStmt.class, sequence(
                comment(),
                child(ObservableProperty.CLASS_DECLARATION)
        ));

        concreteSyntaxModelByClass.put(ReturnStmt.class, sequence(comment(), token(GeneratedJavaParserConstants.RETURN),
                conditional(ObservableProperty.EXPRESSION, IS_PRESENT, sequence(space(), child(ObservableProperty.EXPRESSION))),
                semicolon()));

        concreteSyntaxModelByClass.put(SwitchEntry.class, sequence(
                comment(),
                conditional(ObservableProperty.LABELS, IS_NOT_EMPTY,
                        sequence(token(GeneratedJavaParserConstants.CASE), space(), list(ObservableProperty.LABELS), token(GeneratedJavaParserConstants.COLON)),
                        sequence(token(GeneratedJavaParserConstants._DEFAULT), token(GeneratedJavaParserConstants.COLON))),
                newline(),
                indent(),
                list(ObservableProperty.STATEMENTS, newline(), none(), newline()),
                unindent()
        ));

        concreteSyntaxModelByClass.put(SwitchStmt.class, sequence(
                comment(),
                token(GeneratedJavaParserConstants.SWITCH),
                token(GeneratedJavaParserConstants.LPAREN),
                child(ObservableProperty.SELECTOR),
                token(GeneratedJavaParserConstants.RPAREN),
                space(),
                token(GeneratedJavaParserConstants.LBRACE),
                newline(),
                list(ObservableProperty.ENTRIES, none(), indent(), unindent()),
                token(GeneratedJavaParserConstants.RBRACE)
        ));

        concreteSyntaxModelByClass.put(SwitchExpr.class, sequence(
                comment(),
                token(GeneratedJavaParserConstants.SWITCH),
                token(GeneratedJavaParserConstants.LPAREN),
                child(ObservableProperty.SELECTOR),
                token(GeneratedJavaParserConstants.RPAREN),
                space(),
                token(GeneratedJavaParserConstants.LBRACE),
                newline(),
                list(ObservableProperty.ENTRIES, none(), indent(), unindent()),
                token(GeneratedJavaParserConstants.RBRACE)
        ));

        concreteSyntaxModelByClass.put(SynchronizedStmt.class, sequence(
                comment(),
                token(GeneratedJavaParserConstants.SYNCHRONIZED),
                space(),
                token(LPAREN),
                child(EXPRESSION),
                token(RPAREN),
                space(),
                child(BODY)
        ));

        concreteSyntaxModelByClass.put(ThrowStmt.class, sequence(
                comment(),
                token(GeneratedJavaParserConstants.THROW),
                space(),
                child(ObservableProperty.EXPRESSION),
                semicolon()
        ));

        concreteSyntaxModelByClass.put(TryStmt.class, sequence(
                comment(),
                token(GeneratedJavaParserConstants.TRY),
                space(),
                conditional(ObservableProperty.RESOURCES, CsmConditional.Condition.IS_NOT_EMPTY, sequence(
                        token(LPAREN),
                        list(ObservableProperty.RESOURCES, sequence(semicolon(), newline()), indent(), unindent()),
                        token(RPAREN),
                        space())),
                child(ObservableProperty.TRY_BLOCK),
                list(ObservableProperty.CATCH_CLAUSES),
                conditional(ObservableProperty.FINALLY_BLOCK, IS_PRESENT, sequence(space(), token(GeneratedJavaParserConstants.FINALLY), space(), child(ObservableProperty.FINALLY_BLOCK)))
        ));

        concreteSyntaxModelByClass.put(WhileStmt.class, sequence(
                comment(),
                token(GeneratedJavaParserConstants.WHILE),
                space(),
                token(GeneratedJavaParserConstants.LPAREN),
                child(ObservableProperty.CONDITION),
                token(GeneratedJavaParserConstants.RPAREN),
                space(),
                child(ObservableProperty.BODY)
        ));

        ///
        /// Types
        ///

        concreteSyntaxModelByClass.put(ArrayType.class, sequence(
                child(ObservableProperty.COMPONENT_TYPE),
                list(ObservableProperty.ANNOTATIONS),
                string(GeneratedJavaParserConstants.LBRACKET),
                string(GeneratedJavaParserConstants.RBRACKET)));

        concreteSyntaxModelByClass.put(ClassOrInterfaceType.class, sequence(comment(),
                conditional(SCOPE, IS_PRESENT, sequence(child(SCOPE), string(GeneratedJavaParserConstants.DOT))),
                list(ANNOTATIONS, space()),
                child(NAME),
                conditional(ObservableProperty.USING_DIAMOND_OPERATOR, FLAG,
                        sequence(string(GeneratedJavaParserConstants.LT), string(GeneratedJavaParserConstants.GT)),
                        list(TYPE_ARGUMENTS, sequence(comma(), space()), string(GeneratedJavaParserConstants.LT), string(GeneratedJavaParserConstants.GT)))));

        concreteSyntaxModelByClass.put(IntersectionType.class, sequence(
                comment(),
                annotations(),
                list(ObservableProperty.ELEMENTS, sequence(space(), token(GeneratedJavaParserConstants.BIT_AND), space()))));

        concreteSyntaxModelByClass.put(PrimitiveType.class, sequence(
                comment(),
                list(ObservableProperty.ANNOTATIONS),
                attribute(ObservableProperty.TYPE)));

        concreteSyntaxModelByClass.put(TypeParameter.class, sequence(
                comment(),
                annotations(),
                child(ObservableProperty.NAME),
                list(ObservableProperty.TYPE_BOUND,
                        sequence(
                                space(),
                                token(GeneratedJavaParserConstants.BIT_AND),
                                space()),
                        sequence(
                                space(),
                                token(GeneratedJavaParserConstants.EXTENDS),
                                space()),
                        none())
        ));

        concreteSyntaxModelByClass.put(UnionType.class, sequence(
                comment(),
                annotations(),
                list(ObservableProperty.ELEMENTS, sequence(space(), token(GeneratedJavaParserConstants.BIT_OR), space()))
        ));

        concreteSyntaxModelByClass.put(UnknownType.class, none());

        concreteSyntaxModelByClass.put(VoidType.class, sequence(comment(), annotations(), token(GeneratedJavaParserConstants.VOID)));

        concreteSyntaxModelByClass.put(VarType.class, sequence(comment(), annotations(), string(GeneratedJavaParserConstants.IDENTIFIER, "var")));

        concreteSyntaxModelByClass.put(WildcardType.class, sequence(comment(), annotations(), token(GeneratedJavaParserConstants.HOOK),
                conditional(ObservableProperty.EXTENDED_TYPE, IS_PRESENT, sequence(space(), token(GeneratedJavaParserConstants.EXTENDS), space(), child(EXTENDED_TYPE))),
                conditional(ObservableProperty.SUPER_TYPE, IS_PRESENT, sequence(space(), token(GeneratedJavaParserConstants.SUPER), space(), child(SUPER_TYPE)))));

        ///
        /// Top Level
        ///

        concreteSyntaxModelByClass.put(ArrayCreationLevel.class, sequence(
                annotations(),
                token(GeneratedJavaParserConstants.LBRACKET),
                child(ObservableProperty.DIMENSION),
                token(GeneratedJavaParserConstants.RBRACKET)
        ));

        concreteSyntaxModelByClass.put(CompilationUnit.class, sequence(
                comment(),
                child(ObservableProperty.PACKAGE_DECLARATION),
                list(ObservableProperty.IMPORTS, newline(), none(), sequence(newline(), newline())),
                list(TYPES, newline(), newline(), none(), newline()),
                child(ObservableProperty.MODULE),
                orphanCommentsEnding()));

        concreteSyntaxModelByClass.put(ImportDeclaration.class, sequence(
                comment(),
                token(GeneratedJavaParserConstants.IMPORT),
                space(),
                conditional(ObservableProperty.STATIC, FLAG, sequence(token(GeneratedJavaParserConstants.STATIC), space())),
                child(ObservableProperty.NAME),
                conditional(ASTERISK, FLAG, sequence(token(GeneratedJavaParserConstants.DOT), token(GeneratedJavaParserConstants.STAR))),
                semicolon(),
                orphanCommentsEnding()
        ));

        concreteSyntaxModelByClass.put(PackageDeclaration.class, sequence(
                comment(),
                memberAnnotations(),
                token(GeneratedJavaParserConstants.PACKAGE),
                space(),
                child(ObservableProperty.NAME),
                semicolon(),
                newline(),
                newline(),
                orphanCommentsEnding()));

        ///
        /// Module info
        ///

        concreteSyntaxModelByClass.put(ModuleDeclaration.class, sequence(
                memberAnnotations(),
                conditional(ObservableProperty.OPEN, FLAG, sequence(token(GeneratedJavaParserConstants.OPEN), space())),
                token(GeneratedJavaParserConstants.MODULE),
                space(),
                child(ObservableProperty.NAME),
                space(),
                token(GeneratedJavaParserConstants.LBRACE),
                newline(),
                indent(),
                list(ObservableProperty.DIRECTIVES),
                unindent(),
                token(GeneratedJavaParserConstants.RBRACE),
                newline()
        ));

        concreteSyntaxModelByClass.put(ModuleExportsDirective.class, sequence(
                token(GeneratedJavaParserConstants.EXPORTS),
                space(),
                child(ObservableProperty.NAME),
                list(ObservableProperty.MODULE_NAMES,
                        sequence(comma(), space()),
                        sequence(space(), token(GeneratedJavaParserConstants.TO), space()),
                        none()),
                semicolon(),
                newline()
        ));

        concreteSyntaxModelByClass.put(ModuleOpensDirective.class, sequence(
                token(GeneratedJavaParserConstants.OPENS),
                space(),
                child(ObservableProperty.NAME),
                list(ObservableProperty.MODULE_NAMES,
                        sequence(comma(), space()),
                        sequence(space(), token(GeneratedJavaParserConstants.TO), space()),
                        none()),
                semicolon(),
                newline()
        ));

        concreteSyntaxModelByClass.put(ModuleProvidesDirective.class, sequence(
                token(GeneratedJavaParserConstants.PROVIDES),
                space(),
                child(ObservableProperty.NAME),
                list(ObservableProperty.WITH,
                        sequence(comma(), space()),
                        sequence(space(), token(GeneratedJavaParserConstants.WITH), space()),
                        none()),
                semicolon(),
                newline()
        ));

        concreteSyntaxModelByClass.put(ModuleRequiresDirective.class, sequence(
                token(GeneratedJavaParserConstants.REQUIRES),
                space(),
                modifiers(),
                child(ObservableProperty.NAME),
                semicolon(),
                newline()
        ));

        concreteSyntaxModelByClass.put(ModuleUsesDirective.class, sequence(
                token(GeneratedJavaParserConstants.USES),
                space(),
                child(ObservableProperty.NAME),
                semicolon(),
                newline()
        ));

        List<String> unsupportedNodeClassNames = JavaParserMetaModel.getNodeMetaModels().stream()
                .filter(c -> !c.isAbstract() && !Comment.class.isAssignableFrom(c.getType()) && !concreteSyntaxModelByClass.containsKey(c.getType()))
                .map(nm -> nm.getType().getSimpleName())
                .collect(Collectors.toList());
        if (unsupportedNodeClassNames.isEmpty()) {
            initializationError = Optional.empty();
        } else {
            initializationError = Optional.of("The CSM should include support for these classes: " + String.join(", ", unsupportedNodeClassNames));
        }
    }

    private ConcreteSyntaxModel() {

    }

    public static void genericPrettyPrint(Node node, SourcePrinter printer) {
        forClass(node.getClass()).prettyPrint(node, printer);
    }

    public static String genericPrettyPrint(Node node) {
        SourcePrinter sourcePrinter = new SourcePrinter();
        forClass(node.getClass()).prettyPrint(node, sourcePrinter);
        return sourcePrinter.toString();
    }

    public static CsmElement forClass(Class<? extends Node> nodeClazz) {
        initializationError.ifPresent(s -> {
            throw new IllegalStateException(s);
        });
        if (!concreteSyntaxModelByClass.containsKey(nodeClazz)) {
            throw new UnsupportedOperationException(nodeClazz.getSimpleName());
        }
        return concreteSyntaxModelByClass.get(nodeClazz);
    }

}
