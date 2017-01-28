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

package com.github.javaparser;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.type.ClassOrInterfaceType;

/**
 * The start production for JavaParser.
 * Tells JavaParser what piece of Java code it can expect.
 * For example,
 * COMPILATION_UNIT indicates a complete Java file,
 * and CLASS_BODY would indicate the part of a class that is within { and }.
 *
 * @see JavaParser#parse(ParseStart, Provider)
 */
@FunctionalInterface
public interface ParseStart<R> {
    ParseStart<CompilationUnit> COMPILATION_UNIT = ASTParser::CompilationUnit;
    ParseStart<BlockStmt> BLOCK = ASTParser::Block;
    ParseStart<Statement> STATEMENT = ASTParser::BlockStatement;
    ParseStart<ImportDeclaration> IMPORT_DECLARATION = ASTParser::ImportDeclaration;
    ParseStart<Expression> EXPRESSION = ASTParser::Expression;
    ParseStart<AnnotationExpr> ANNOTATION = ASTParser::Annotation;
    ParseStart<BodyDeclaration<?>> ANNOTATION_BODY = ASTParser::AnnotationBodyDeclaration;
    ParseStart<BodyDeclaration<?>> CLASS_BODY = p -> p.ClassOrInterfaceBodyDeclaration(false);
    ParseStart<BodyDeclaration<?>> INTERFACE_BODY = p -> p.ClassOrInterfaceBodyDeclaration(true);
    ParseStart<ClassOrInterfaceType> CLASS_OR_INTERFACE_TYPE = ASTParser::ClassOrInterfaceType;
    ParseStart<VariableDeclarationExpr> VARIABLE_DECLARATION_EXPR = ASTParser::VariableDeclarationExpression;
    ParseStart<ExplicitConstructorInvocationStmt> EXPLICIT_CONSTRUCTOR_INVOCATION_STMT = ASTParser::ExplicitConstructorInvocation;

    R parse(ASTParser parser) throws ParseException;
}
