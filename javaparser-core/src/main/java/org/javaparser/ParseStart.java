/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2020 The JavaParser Team.
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

package org.javaparser;

import org.javaparser.ast.CompilationUnit;
import org.javaparser.ast.ImportDeclaration;
import org.javaparser.ast.PackageDeclaration;
import org.javaparser.ast.body.BodyDeclaration;
import org.javaparser.ast.body.MethodDeclaration;
import org.javaparser.ast.body.Parameter;
import org.javaparser.ast.body.TypeDeclaration;
import org.javaparser.ast.expr.*;
import org.javaparser.ast.modules.ModuleDeclaration;
import org.javaparser.ast.modules.ModuleDirective;
import org.javaparser.ast.stmt.BlockStmt;
import org.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import org.javaparser.ast.stmt.Statement;
import org.javaparser.ast.type.ClassOrInterfaceType;
import org.javaparser.ast.type.Type;
import org.javaparser.ast.type.TypeParameter;

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
    ParseStart<CompilationUnit> COMPILATION_UNIT = GeneratedJavaParser::CompilationUnit;
    ParseStart<BlockStmt> BLOCK = GeneratedJavaParser::BlockParseStart;
    ParseStart<Statement> STATEMENT = GeneratedJavaParser::BlockStatementParseStart;
    ParseStart<ImportDeclaration> IMPORT_DECLARATION = GeneratedJavaParser::ImportDeclarationParseStart;
    ParseStart<Expression> EXPRESSION = GeneratedJavaParser::ExpressionParseStart;
    ParseStart<AnnotationExpr> ANNOTATION = GeneratedJavaParser::AnnotationParseStart;
    ParseStart<BodyDeclaration<?>> ANNOTATION_BODY = GeneratedJavaParser::AnnotationBodyDeclarationParseStart;
    ParseStart<BodyDeclaration<?>> CLASS_BODY = GeneratedJavaParser::ClassOrInterfaceBodyDeclarationParseStart;
    ParseStart<ClassOrInterfaceType> CLASS_OR_INTERFACE_TYPE = GeneratedJavaParser::ClassOrInterfaceTypeParseStart;
    ParseStart<Type> TYPE = GeneratedJavaParser::ResultTypeParseStart;
    ParseStart<TypeParameter> TYPE_PARAMETER = GeneratedJavaParser::TypeParameterParseStart;
    ParseStart<VariableDeclarationExpr> VARIABLE_DECLARATION_EXPR = GeneratedJavaParser::VariableDeclarationExpressionParseStart;
    ParseStart<ExplicitConstructorInvocationStmt> EXPLICIT_CONSTRUCTOR_INVOCATION_STMT = GeneratedJavaParser::ExplicitConstructorInvocationParseStart;
    ParseStart<Name> NAME = GeneratedJavaParser::NameParseStart;
    ParseStart<SimpleName> SIMPLE_NAME = GeneratedJavaParser::SimpleNameParseStart;
    ParseStart<Parameter> PARAMETER = GeneratedJavaParser::ParameterParseStart;
    ParseStart<PackageDeclaration> PACKAGE_DECLARATION = GeneratedJavaParser::PackageDeclarationParseStart;
    ParseStart<TypeDeclaration<?>> TYPE_DECLARATION = GeneratedJavaParser::TypeDeclarationParseStart;
    ParseStart<ModuleDeclaration> MODULE_DECLARATION = GeneratedJavaParser::ModuleDeclarationParseStart;
    ParseStart<ModuleDirective> MODULE_DIRECTIVE = GeneratedJavaParser::ModuleDirectiveParseStart;
    ParseStart<MethodDeclaration> METHOD_DECLARATION = GeneratedJavaParser::MethodDeclarationParseStart;

    R parse(GeneratedJavaParser parser) throws ParseException;
}
