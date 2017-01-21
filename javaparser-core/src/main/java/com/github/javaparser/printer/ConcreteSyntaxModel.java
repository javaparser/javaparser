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
import static com.github.javaparser.printer.concretesyntaxmodel.CsmConditional.Condition.FLAG;
import static com.github.javaparser.printer.concretesyntaxmodel.CsmConditional.Condition.IS_EMPTY;
import static com.github.javaparser.printer.concretesyntaxmodel.CsmConditional.Condition.IS_NOT_EMPTY;
import static com.github.javaparser.printer.concretesyntaxmodel.CsmElement.*;
import static com.github.javaparser.utils.PositionUtils.sortByBeginPosition;

/**
 * The Concrete Syntax Model for a single node type. It knows the syntax used to represent a certain element in Java
 * code.
 */
public class ConcreteSyntaxModel {

    static Map<Class, CsmElement> concreteSyntaxModelByClass = new HashMap<>();

    static {
        concreteSyntaxModelByClass.put(CompilationUnit.class, sequence(
                    comment(),
                    child(ObservableProperty.PACKAGE_DECLARATION),
                    list(ObservableProperty.IMPORTS, newline()),
                    list(TYPES, newline()),
                    orphanCommentsEnding()));

        concreteSyntaxModelByClass.put(SimpleName.class, attribute(ObservableProperty.IDENTIFIER));

        concreteSyntaxModelByClass.put(ClassOrInterfaceDeclaration.class, sequence(
                    comment(),
                    list(ObservableProperty.ANNOTATIONS, newline(), null, newline()),
                    list(ObservableProperty.MODIFIERS, space()),
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
                    block(list(ObservableProperty.MEMBERS, null, null, newline())),
                    newline()));

        concreteSyntaxModelByClass.put(ClassOrInterfaceType.class, sequence(comment(),
                    conditional(SCOPE, CsmConditional.Condition.IS_PRESENT, sequence(child(SCOPE), string(ASTParserConstants.DOT))),
                    list(ANNOTATIONS, space()),
                    child(NAME),
                    conditional(ObservableProperty.DIAMOND_OPERATOR, FLAG,
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
                    list(ObservableProperty.MODIFIERS),
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
