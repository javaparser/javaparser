package com.github.javaparser;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.Statement;

import java.util.List;

@FunctionalInterface
public interface ParseContext<R> {
	ParseContext<CompilationUnit> COMPILATION_UNIT = ASTParser::CompilationUnit;
	ParseContext<BlockStmt> BLOCK = ASTParser::Block;
	ParseContext<List<Statement>> STATEMENTS = ASTParser::Statements;
	ParseContext<Statement> STATEMENT = ASTParser::Statement;
	ParseContext<ImportDeclaration> IMPORT_DECLARATION= ASTParser::ImportDeclaration;
	ParseContext<Expression> EXPRESSION = ASTParser::Expression;
	ParseContext<AnnotationExpr> ANNOTATION = ASTParser::Annotation;
	ParseContext<BodyDeclaration<?>> ANNOTATION_BODY = ASTParser::AnnotationBodyDeclaration;
	ParseContext<BodyDeclaration<?>> CLASS_BODY = p -> p.ClassOrInterfaceBodyDeclaration(false);
	ParseContext<BodyDeclaration<?>> INTERFACE_BODY = p -> p.ClassOrInterfaceBodyDeclaration(true);

	R parse(ASTParser parser) throws ParseException;
}