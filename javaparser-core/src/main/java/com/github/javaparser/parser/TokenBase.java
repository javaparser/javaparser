package com.github.javaparser.parser;

import com.github.javaparser.ast.lexical.Lexeme;

/**
 * @author Didier Villevalois
 */
class TokenBase {

	/* Special management of GT to ease generics */
	int realKind = ASTParserConstants.GT;

	Lexeme lexeme;
}
