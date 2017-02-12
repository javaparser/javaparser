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
import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.observer.*;
import com.github.javaparser.ast.observer.Observable;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;
import com.github.javaparser.printer.concretesyntaxmodel.*;

import java.util.*;

import static com.github.javaparser.ast.observer.ObservableProperty.*;
import static com.github.javaparser.printer.concretesyntaxmodel.CsmConditional.Condition.*;
import static com.github.javaparser.printer.concretesyntaxmodel.CsmElement.*;
import static com.github.javaparser.printer.concretesyntaxmodel.CsmElement.conditional;
import static com.github.javaparser.printer.concretesyntaxmodel.CsmElement.list;
import static com.github.javaparser.utils.PositionUtils.sortByBeginPosition;

/**
 * The Concrete Syntax Model for a single node type. It knows the syntax used to represent a certain element in Java
 * code.
 */
public class ConcreteSyntaxModel {

    static Map<Class, CsmElement> concreteSyntaxModelByClass = new HashMap<>();

    private static CsmElement modifiers() {
        return list(ObservableProperty.MODIFIERS, space(), none(), space());
    }

    private static CsmElement memberAnnotations() {
        return list(ObservableProperty.ANNOTATIONS, none(), none(), newline());
    }

    private static CsmElement annotations() {
        return list(ObservableProperty.ANNOTATIONS, none(), none(), newline());
    }

    private static CsmElement typeParameters() {
        return list(ObservableProperty.TYPE_PARAMETERS, none(), space(), space());
    }

    private static CsmElement typeArguments() {
        return list(ObservableProperty.TYPE_ARGUMENTS, none(), space(), space());
    }

    static {

        ///
        /// Comments
        ///


        ///
        /// Top Level
        ///

        concreteSyntaxModelByClass.put(CompilationUnit.class, sequence(
                    comment(),
                    child(ObservableProperty.PACKAGE_DECLARATION),
                    list(ObservableProperty.IMPORTS, none(), none(), newline()),
                    list(TYPES, newline()),
                    orphanCommentsEnding()));

        concreteSyntaxModelByClass.put(PackageDeclaration.class, sequence(
                comment(),
                list(ObservableProperty.ANNOTATIONS),
                token(ASTParserConstants.PACKAGE),
                space(),
                child(ObservableProperty.NAME),
                semicolon(),
                newline(),
                newline(),
                orphanCommentsEnding()));

        concreteSyntaxModelByClass.put(Name.class, sequence(
                comment(),
                conditional(ObservableProperty.QUALIFIER, IS_PRESENT, sequence(child(ObservableProperty.QUALIFIER), token(ASTParserConstants.DOT))),
                attribute(IDENTIFIER),
                orphanCommentsEnding()
        ));

        concreteSyntaxModelByClass.put(ImportDeclaration.class, sequence(
                comment(),
                token(ASTParserConstants.IMPORT),
                space(),
                conditional(STATIC, FLAG, sequence(token(ASTParserConstants.STATIC), space())),
                child(ObservableProperty.NAME),
                conditional(IS_ASTERISK, FLAG, sequence(token(ASTParserConstants.DOT), token(ASTParserConstants.STAR))),
                semicolon(),
                newline(),
                orphanCommentsEnding()
        ));

        concreteSyntaxModelByClass.put(SimpleName.class, attribute(ObservableProperty.IDENTIFIER));

        concreteSyntaxModelByClass.put(ConstructorDeclaration.class, sequence(
                comment(),
                memberAnnotations(),
                modifiers(),
                typeParameters(),
                conditional(ObservableProperty.IS_GENERIC, FLAG, space()),
                child(ObservableProperty.NAME),
                token(ASTParserConstants.LPAREN),
                list(ObservableProperty.PARAMETERS, sequence(comma(), space()), none(), none()),
                token(ASTParserConstants.RPAREN),
                list(ObservableProperty.THROWN_EXCEPTIONS, sequence(space(), token(ASTParserConstants.THROWS), space()), none(), sequence(comma(), space())),
                space(),
                child(ObservableProperty.BODY)
        ));

        concreteSyntaxModelByClass.put(Parameter.class, sequence(
                comment(),
                annotations(),
                modifiers(),
                child(ObservableProperty.TYPE),
                conditional(ObservableProperty.VAR_ARGS, FLAG, token(ASTParserConstants.ELLIPSIS)),
                space(),
                child(ObservableProperty.NAME)));

        concreteSyntaxModelByClass.put(BlockStmt.class, sequence(
                orphanCommentsBeforeThis(),
                comment(),
                token(ASTParserConstants.LBRACE),
                newline(),
                list(ObservableProperty.STATEMENTS, newline(), indent(), sequence(newline(), unindent())),
                orphanCommentsEnding(),
                token(ASTParserConstants.RBRACE)
        ));

        concreteSyntaxModelByClass.put(ExpressionStmt.class, sequence(
            orphanCommentsBeforeThis(),
            comment(),
            child(ObservableProperty.EXPRESSION),
            semicolon()
        ));

        concreteSyntaxModelByClass.put(MethodDeclaration.class, sequence(
                orphanCommentsBeforeThis(),
                comment(),
                memberAnnotations(),
                modifiers(),
                conditional(ObservableProperty.IS_DEFAULT, FLAG, sequence(token(ASTParserConstants.DEFAULT), space())),
                typeParameters(),
                child(ObservableProperty.TYPE),
                space(),
                child(ObservableProperty.NAME),
                token(ASTParserConstants.LPAREN),
                list(ObservableProperty.PARAMETERS, sequence(comma(), space()), none(), none()),
                token(ASTParserConstants.RPAREN),
                list(ObservableProperty.THROWN_EXCEPTIONS, sequence(space(), token(ASTParserConstants.THROWS), space()), none(), sequence(comma(), space())),
                conditional(ObservableProperty.BODY, IS_PRESENT, sequence(space(), child(ObservableProperty.BODY)), semicolon())
        ));

        concreteSyntaxModelByClass.put(ClassOrInterfaceDeclaration.class, sequence(
                    comment(),
                    list(ObservableProperty.ANNOTATIONS, newline(), none(), newline()),
                    modifiers(),
                    conditional(ObservableProperty.IS_INTERFACE, FLAG, token(ASTParserConstants.INTERFACE), token(ASTParserConstants.CLASS)),
                    space(),
                    child(ObservableProperty.NAME),
                    list(TYPE_PARAMETERS, sequence(comma(), space()), string(ASTParserConstants.LT), string(ASTParserConstants.GT)),
                    list(ObservableProperty.EXTENDED_TYPES, sequence(
                            space(),
                            token(ASTParserConstants.EXTENDS),
                            space()), none(), sequence(string(ASTParserConstants.COMMA), space())),
                    list(ObservableProperty.IMPLEMENTED_TYPES, sequence(string(ASTParserConstants.COMMA), space()), sequence(
                            space(),
                            token(ASTParserConstants.IMPLEMENTS),
                            space()), none()),
                    space(),
                    block(sequence(newline(), newline(), list(ObservableProperty.MEMBERS, sequence(newline(), newline()), none(), newline()))),
                    newline()));

        concreteSyntaxModelByClass.put(ClassOrInterfaceType.class, sequence(comment(),
                    conditional(SCOPE, IS_PRESENT, sequence(child(SCOPE), string(ASTParserConstants.DOT))),
                    list(ANNOTATIONS, space()),
                    child(NAME),
                    conditional(ObservableProperty.USING_DIAMOND_OPERATOR, FLAG,
                            sequence(string(ASTParserConstants.LT), string(ASTParserConstants.GT)),
                            list(TYPE_ARGUMENTS, sequence(comma(), space()), string(ASTParserConstants.LT), string(ASTParserConstants.GT)))));

        concreteSyntaxModelByClass.put(PrimitiveType.class, sequence(
                    comment(),
                    list(ObservableProperty.ANNOTATIONS),
                    attribute(ObservableProperty.TYPE)));

        concreteSyntaxModelByClass.put(ArrayType.class, sequence(
                    child(ObservableProperty.COMPONENT_TYPE),
                    list(ObservableProperty.ANNOTATIONS),
                    string(ASTParserConstants.LBRACKET),
                    string(ASTParserConstants.RBRACKET)));

        concreteSyntaxModelByClass.put(FieldDeclaration.class, sequence(
                    orphanCommentsBeforeThis(),
                    comment(),
                    list(ObservableProperty.ANNOTATIONS),
                    modifiers(),
                    conditional(ObservableProperty.VARIABLES, IS_NOT_EMPTY, child(ObservableProperty.MAXIMUM_COMMON_TYPE)),
                    space(),
                    list(ObservableProperty.VARIABLES, sequence(comma(), space())),
                    semicolon()));

        // FIXME array levels
        concreteSyntaxModelByClass.put(VariableDeclarator.class, sequence(
                    comment(),
                    child(ObservableProperty.NAME),
                    conditional(ObservableProperty.INITIALIZER, IS_PRESENT, sequence(space(), token(ASTParserConstants.ASSIGN), space(),
                            child(ObservableProperty.INITIALIZER)))
        ));

        concreteSyntaxModelByClass.put(ClassExpr.class, sequence(
                comment(), child(ObservableProperty.TYPE), token(ASTParserConstants.DOT), token(ASTParserConstants.CLASS)));

        concreteSyntaxModelByClass.put(AssignExpr.class, sequence(
            comment(),
            child(ObservableProperty.TARGET),
            space(),
            attribute(ObservableProperty.OPERATOR),
            space(),
            child(ObservableProperty.VALUE)
        ));

        concreteSyntaxModelByClass.put(NameExpr.class, sequence(
           comment(),
           child(ObservableProperty.NAME),
           orphanCommentsEnding()
        ));

        concreteSyntaxModelByClass.put(ObjectCreationExpr.class, sequence(
            comment(),
            conditional(ObservableProperty.SCOPE, IS_PRESENT, sequence(child(ObservableProperty.SCOPE), token(ASTParserConstants.DOT))),
            token(ASTParserConstants.NEW),
            space(),
            list(ObservableProperty.TYPE_ARGUMENTS),
            conditional(ObservableProperty.TYPE_ARGUMENTS, IS_NOT_EMPTY, space()),
            child(ObservableProperty.TYPE),
            token(ASTParserConstants.LPAREN),
            list(ObservableProperty.ARGUMENTS, sequence(comma(), space()), none(), none()),
            token(ASTParserConstants.RPAREN),
            conditional(ObservableProperty.ANONYMOUS_CLASS_BODY, IS_PRESENT, sequence(
                    space(),
                    child(ObservableProperty.ANONYMOUS_CLASS_BODY)))
        ));

        concreteSyntaxModelByClass.put(MethodCallExpr.class, sequence(
            comment(),
            conditional(ObservableProperty.SCOPE, IS_PRESENT, sequence(child(ObservableProperty.SCOPE), token(ASTParserConstants.DOT))),
            typeArguments(),
            child(ObservableProperty.NAME),
            token(ASTParserConstants.LPAREN),
            list(ObservableProperty.ARGUMENTS, sequence(comma(), space()), none(), none()),
            token(ASTParserConstants.RPAREN)
        ));

        concreteSyntaxModelByClass.put(VoidType.class, sequence(comment(), annotations(), token(ASTParserConstants.VOID)));

        concreteSyntaxModelByClass.put(WildcardType.class, sequence(comment(), annotations(), token(ASTParserConstants.HOOK),
                list(ObservableProperty.EXTENDED_TYPES, sequence(space(), token(ASTParserConstants.EXTENDS), space()), none(), sequence(comma(), space())),
                list(ObservableProperty.SUPER_TYPES, sequence(space(), token(ASTParserConstants.SUPER), space()), none(), sequence(comma(), space()))));


        concreteSyntaxModelByClass.put(MarkerAnnotationExpr.class, sequence(comment(), token(ASTParserConstants.AT), attribute(ObservableProperty.NAME)));

        concreteSyntaxModelByClass.put(ReturnStmt.class, sequence(comment(), token(ASTParserConstants.RETURN),
                conditional(ObservableProperty.EXPRESSION, IS_PRESENT, sequence(space(), child(ObservableProperty.EXPRESSION))),
                semicolon()));

        concreteSyntaxModelByClass.put(IfStmt.class, sequence(
                comment(),
                token(ASTParserConstants.IF),
                space(),
                token(ASTParserConstants.LPAREN),
                child(ObservableProperty.CONDITION),
                token(ASTParserConstants.RPAREN),
                CsmElement.conditional(ObservableProperty.THEN_BLOCK, CsmConditional.Condition.FLAG,
                        CsmElement.sequence(CsmElement.space(), child(ObservableProperty.THEN_STMT),
                                CsmElement.conditional(ObservableProperty.ELSE_STMT, IS_PRESENT, CsmElement.space())),
                        CsmElement.sequence(CsmElement.newline(), CsmElement.indent(), child(ObservableProperty.THEN_STMT),
                                CsmElement.conditional(ObservableProperty.ELSE_STMT, IS_PRESENT, CsmElement.newline()),
                                CsmElement.unindent())),
                conditional(ObservableProperty.ELSE_STMT, IS_PRESENT,
                        CsmElement.sequence(CsmElement.token(ASTParserConstants.ELSE),
                            CsmElement.conditional(ObservableProperty.ELSE_BLOCK, CsmConditional.Condition.FLAG,
                                    CsmElement.sequence(CsmElement.space(), child(ObservableProperty.ELSE_STMT)),
                                    CsmElement.sequence(CsmElement.newline(), CsmElement.indent(), child(ObservableProperty.ELSE_STMT), CsmElement.unindent()))))
        ));

        concreteSyntaxModelByClass.put(ForeachStmt.class, sequence(
                comment(),
                token(ASTParserConstants.FOR),
                space(),
                token(ASTParserConstants.LPAREN),
                child(ObservableProperty.VARIABLE),
                space(),
                token(ASTParserConstants.COLON),
                space(),
                child(ObservableProperty.ITERABLE),
                token(ASTParserConstants.RPAREN),
                space(),
                child(ObservableProperty.BODY)
        ));

        concreteSyntaxModelByClass.put(VariableDeclarationExpr.class, sequence(
                comment(),
                annotations(),
                modifiers(),
                child(ObservableProperty.MAXIMUM_COMMON_TYPE),
                space(),
                list(ObservableProperty.VARIABLES, sequence(comma(), space()))
        ));

        concreteSyntaxModelByClass.put(StringLiteralExpr.class, sequence(
                comment(),
                stringToken(ObservableProperty.VALUE)
        ));
        concreteSyntaxModelByClass.put(ThisExpr.class, sequence(
                comment(),
                conditional(ObservableProperty.CLASS_EXPR, IS_PRESENT, sequence(child(CLASS_EXPR), token(ASTParserConstants.DOT))),
                token(ASTParserConstants.THIS)
        ));

        concreteSyntaxModelByClass.put(ForStmt.class, sequence(
                comment(),
                token(ASTParserConstants.FOR),
                space(),
                token(ASTParserConstants.LPAREN),
                list(ObservableProperty.INITIALIZATION, sequence(comma(), space())),
                semicolon(),
                space(),
                child(ObservableProperty.COMPARE),
                semicolon(),
                space(),
                list(ObservableProperty.UPDATE, sequence(comma(), space())),
                token(ASTParserConstants.RPAREN),
                space(),
                child(ObservableProperty.BODY)
        ));

        concreteSyntaxModelByClass.put(BooleanLiteralExpr.class, sequence(
                comment(), attribute(VALUE)
        ));
        concreteSyntaxModelByClass.put(WhileStmt.class, sequence(
                comment(),
                token(ASTParserConstants.WHILE),
                space(),
                token(ASTParserConstants.LPAREN),
                child(ObservableProperty.CONDITION),
                token(ASTParserConstants.RPAREN),
                space(),
                child(ObservableProperty.BODY)
        ));

        concreteSyntaxModelByClass.put(LambdaExpr.class, sequence(
                comment(),
                conditional(ObservableProperty.ENCLOSING_PARAMETERS, FLAG, token(ASTParserConstants.LPAREN)),
                list(ObservableProperty.PARAMETERS, sequence(comma(), space())),
                conditional(ObservableProperty.ENCLOSING_PARAMETERS, FLAG, token(ASTParserConstants.RPAREN)),
                space(),
                token(ASTParserConstants.ARROW),
                space(),
                CsmElement.conditional(ObservableProperty.EXPRESSION_BODY, IS_PRESENT, child(ObservableProperty.EXPRESSION_BODY), child(ObservableProperty.BODY))
        ));

        concreteSyntaxModelByClass.put(CharLiteralExpr.class, sequence(
                comment(),
                charToken(ObservableProperty.VALUE)
        ));

        concreteSyntaxModelByClass.put(BinaryExpr.class, sequence(
                comment(),
                child(ObservableProperty.LEFT),
                space(),
                attribute(ObservableProperty.OPERATOR),
                space(),
                child(ObservableProperty.RIGHT)
        ));

        concreteSyntaxModelByClass.put(UnaryExpr.class, sequence(
                conditional(ObservableProperty.IS_PREFIX, FLAG, attribute(ObservableProperty.OPERATOR)),
                child(ObservableProperty.EXPRESSION),
                conditional(ObservableProperty.IS_POSTFIX, FLAG, attribute(ObservableProperty.OPERATOR))
        ));

        concreteSyntaxModelByClass.put(InstanceOfExpr.class, sequence(
                comment(),
                child(ObservableProperty.EXPRESSION),
                space(),
                token(ASTParserConstants.INSTANCEOF),
                space(),
                child(ObservableProperty.TYPE)
        ));

        concreteSyntaxModelByClass.put(EnclosedExpr.class, sequence(
                comment(),
                token(ASTParserConstants.LPAREN),
                child(ObservableProperty.INNER),
                token(ASTParserConstants.RPAREN)
        ));

        concreteSyntaxModelByClass.put(ThrowStmt.class, sequence(
                comment(),
                token(ASTParserConstants.THROW),
                space(),
                child(ObservableProperty.EXPRESSION),
                semicolon()
        ));
        concreteSyntaxModelByClass.put(IntegerLiteralExpr.class, sequence(
                comment(),
                attribute(ObservableProperty.VALUE)
        ));
        concreteSyntaxModelByClass.put(LongLiteralExpr.class, sequence(
                comment(),
                attribute(ObservableProperty.VALUE)
        ));
        concreteSyntaxModelByClass.put(DoubleLiteralExpr.class, sequence(
                comment(),
                attribute(ObservableProperty.VALUE)
        ));
        concreteSyntaxModelByClass.put(MethodReferenceExpr.class, sequence(
                comment(),
                child(ObservableProperty.SCOPE),
                token(ASTParserConstants.DOUBLECOLON),
                typeArguments(),
                attribute(ObservableProperty.IDENTIFIER)
        ));

        concreteSyntaxModelByClass.put(NullLiteralExpr.class, sequence(
                comment(),
                token(ASTParserConstants.NULL)
        ));
        concreteSyntaxModelByClass.put(TypeExpr.class, sequence(
                comment(),
                child(ObservableProperty.TYPE)
        ));
        concreteSyntaxModelByClass.put(CastExpr.class, sequence(
                comment(),
                token(ASTParserConstants.LPAREN),
                child(ObservableProperty.TYPE),
                token(ASTParserConstants.RPAREN),
                space(),
                child(ObservableProperty.EXPRESSION)
        ));
        concreteSyntaxModelByClass.put(UnknownType.class, none());

        concreteSyntaxModelByClass.put(TypeParameter.class, CsmElement.sequence(
                CsmElement.comment(),
                annotations(),
                CsmElement.child(ObservableProperty.NAME),
                CsmElement.list(ObservableProperty.TYPE_BOUND,
                        CsmElement.sequence(
                            CsmElement.space(),
                            CsmElement.token(ASTParserConstants.BIT_AND),
                            CsmElement.space()),
                        CsmElement.sequence(
                                CsmElement.space(),
                                CsmElement.token(ASTParserConstants.EXTENDS),
                                CsmElement.space()),
                        CsmElement.none())
        ));

        concreteSyntaxModelByClass.put(ArrayCreationExpr.class, CsmElement.sequence(
                CsmElement.comment(),
                CsmElement.token(ASTParserConstants.NEW),
                CsmElement.space(),
                CsmElement.list(ObservableProperty.LEVELS),
                CsmElement.conditional(ObservableProperty.INITIALIZER, IS_PRESENT, CsmElement.sequence(CsmElement.space(), CsmElement.child(ObservableProperty.INITIALIZER)))
        ));

        concreteSyntaxModelByClass.put(ArrayCreationLevel.class, CsmElement.sequence(
                annotations(),
                token(ASTParserConstants.LBRACKET),
                CsmElement.child(ObservableProperty.DIMENSION),
                token(ASTParserConstants.RBRACKET)
        ));

        concreteSyntaxModelByClass.put(EmptyMemberDeclaration.class, CsmElement.sequence(CsmElement.comment(), CsmElement.token(ASTParserConstants.SEMICOLON)));

        concreteSyntaxModelByClass.put(InitializerDeclaration.class, CsmElement.sequence(
                CsmElement.comment(),
                CsmElement.conditional(ObservableProperty.STATIC, FLAG, CsmElement.sequence(CsmElement.token(ASTParserConstants.STATIC), CsmElement.space())),
                CsmElement.child(ObservableProperty.BODY)));

        concreteSyntaxModelByClass.put(NormalAnnotationExpr.class, CsmElement.sequence(
                CsmElement.comment(),
                CsmElement.token(ASTParserConstants.AT),
                CsmElement.child(ObservableProperty.NAME),
                token(ASTParserConstants.LPAREN),
                CsmElement.list(ObservableProperty.PAIRS, CsmElement.sequence(CsmElement.comma(), CsmElement.space())),
                token(ASTParserConstants.RPAREN)
        ));

        concreteSyntaxModelByClass.put(ArrayInitializerExpr.class, CsmElement.sequence(
                CsmElement.comment(),
                CsmElement.token(ASTParserConstants.LBRACE),
                CsmElement.list(ObservableProperty.VALUES, CsmElement.sequence(CsmElement.comma(), CsmElement.space()), CsmElement.space(), CsmElement.space()),
                CsmElement.token(ASTParserConstants.RBRACE)));

        concreteSyntaxModelByClass.put(EnumDeclaration.class, CsmElement.sequence(
                CsmElement.comment(),
                annotations(),
                modifiers(),
                CsmElement.token(ASTParserConstants.ENUM),
                CsmElement.space(),
                CsmElement.child(ObservableProperty.NAME),
                list(ObservableProperty.IMPLEMENTED_TYPES,
                        CsmElement.sequence(CsmElement.comma(), CsmElement.space()),
                        CsmElement.sequence(CsmElement.space(), CsmElement.token(ASTParserConstants.IMPLEMENTS), CsmElement.space()),
                        CsmElement.none()),
                CsmElement.space(),
                CsmElement.token(ASTParserConstants.LBRACE),
                CsmElement.indent(),
                CsmElement.list(ObservableProperty.ENTRIES,
                        CsmElement.sequence(CsmElement.comma(), CsmElement.space()),
                        CsmElement.newline(),
                        CsmElement.none()),
                CsmElement.conditional(ObservableProperty.MEMBERS, IS_EMPTY,
                        CsmElement.conditional(ObservableProperty.ENTRIES, IS_NOT_EMPTY, CsmElement.newline()),
                        CsmElement.sequence(CsmElement.semicolon(), CsmElement.newline(), CsmElement.list(ObservableProperty.MEMBERS, CsmElement.newline(), CsmElement.newline(), CsmElement.none(), CsmElement.none()))),
                CsmElement.unindent(),
                CsmElement.token(ASTParserConstants.RBRACE)
        ));

    }

    private ConcreteSyntaxModel() {

    }

    public static void genericPrettyPrint(Node node, SourcePrinter printer) {
        forClass(node.getClass()).prettyPrint(node, printer);
    }

    public static String genericPrettyPrint(Node node) {
        SourcePrinter sourcePrinter = new SourcePrinter("    ");
        forClass(node.getClass()).prettyPrint(node, sourcePrinter);
        return sourcePrinter.getSource();
    }

    public static CsmElement forClass(Class<? extends Node> nodeClazz) {
        if (!concreteSyntaxModelByClass.containsKey(nodeClazz)) {
            throw new UnsupportedOperationException(nodeClazz.getSimpleName());
        }
        return concreteSyntaxModelByClass.get(nodeClazz);
    }

}
