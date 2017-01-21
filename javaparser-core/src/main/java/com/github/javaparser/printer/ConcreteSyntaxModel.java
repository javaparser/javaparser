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
import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.ClassExpr;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.observer.*;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.printer.concretesyntaxmodel.*;

import java.util.*;

import static com.github.javaparser.ast.observer.ObservableProperty.*;
import static com.github.javaparser.printer.concretesyntaxmodel.CsmConditional.Condition.FLAG;
import static com.github.javaparser.printer.concretesyntaxmodel.CsmConditional.Condition.IS_NOT_EMPTY;
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
                    list(ObservableProperty.IMPORTS, newline()),
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

        concreteSyntaxModelByClass.put(Name.class, attribute(IDENTIFIER));

        concreteSyntaxModelByClass.put(ImportDeclaration.class, sequence(
                comment(),
                token(ASTParserConstants.IMPORT),
                space(),
                conditional(IS_STATIC, FLAG, sequence(token(ASTParserConstants.STATIC), space())),
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
                list(ObservableProperty.PARAMETERS, none(), none(), sequence(comma(), space())),
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

        concreteSyntaxModelByClass.put(ClassOrInterfaceDeclaration.class, sequence(
                    comment(),
                    list(ObservableProperty.ANNOTATIONS, newline(), null, newline()),
                    modifiers(),
                    conditional(ObservableProperty.IS_INTERFACE, FLAG, token(ASTParserConstants.INTERFACE), token(ASTParserConstants.CLASS)),
                    space(),
                    child(ObservableProperty.NAME),
                    list(TYPE_PARAMETERS, sequence(comma(), space()), string(ASTParserConstants.LT), string(ASTParserConstants.GT)),
                    list(ObservableProperty.EXTENDED_TYPES, sequence(
                            space(),
                            string(ASTParserConstants.EXTENDS),
                            space()), null, sequence(string(ASTParserConstants.COMMA), space())),
                    list(ObservableProperty.IMPLEMENTED_TYPES, sequence(
                            space(),
                            string(ASTParserConstants.IMPLEMENTS),
                            space()), null, sequence(string(ASTParserConstants.COMMA), space())),
                    space(),
                    block(sequence(newline(), newline(), list(ObservableProperty.MEMBERS, newline(), none(), newline()))),
                    newline()));

        concreteSyntaxModelByClass.put(ClassOrInterfaceType.class, sequence(comment(),
                    conditional(SCOPE, CsmConditional.Condition.IS_PRESENT, sequence(child(SCOPE), string(ASTParserConstants.DOT))),
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
                    list(ObservableProperty.VARIABLES, sequence(comma(), space(), null, null)),
                    semicolon()));

        concreteSyntaxModelByClass.put(VariableDeclarator.class, sequence(
                    comment(),
                    child(ObservableProperty.NAME)));

        concreteSyntaxModelByClass.put(ClassExpr.class, sequence(
                comment(), child(ObservableProperty.TYPE), token(ASTParserConstants.DOT), token(ASTParserConstants.CLASS)));
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
