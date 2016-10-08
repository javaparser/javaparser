package com.github.javaparser;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.Statement;

/**
 * The start production for JavaParser.
 * Tells JavaParser what piece of Java code it can expect.
 * For example,
 * COMPILATION_UNIT indicates a complete Java file,
 * and CLASS_BODY would indicate the part of a class that is within { and }.
 * @see JavaParser#parse(ParseStart, Provider)
 */
@FunctionalInterface
public interface ParseStart<R> {
	ParseStart<CompilationUnit> COMPILATION_UNIT = ASTParser::CompilationUnit;
	ParseStart<BlockStmt> BLOCK = ASTParser::Block;
	ParseStart<Statement> STATEMENT = ASTParser::BlockStatement;
	ParseStart<ImportDeclaration> IMPORT_DECLARATION= ASTParser::ImportDeclaration;
	ParseStart<Expression> EXPRESSION = ASTParser::Expression;
	ParseStart<AnnotationExpr> ANNOTATION = ASTParser::Annotation;
	ParseStart<BodyDeclaration<?>> ANNOTATION_BODY = ASTParser::AnnotationBodyDeclaration;
	ParseStart<BodyDeclaration<?>> CLASS_BODY = p -> p.ClassOrInterfaceBodyDeclaration(false);
	ParseStart<BodyDeclaration<?>> INTERFACE_BODY = p -> p.ClassOrInterfaceBodyDeclaration(true);

	R parse(ASTParser parser) throws ParseException;
}
