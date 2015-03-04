package com.github.javaparser.ast.lexical;

/**
 * @author Didier Villevalois
 */
public abstract class Run {

	private Lexeme first;
	private Lexeme last;

//	public abstract Run enclosing();

//	public abstract List<Run> enclosed();

	public Lexeme first() {
		return first;
	}

	public Lexeme last() {
		return last;
	}

	public void setFirst(Lexeme first) {
		this.first = first;
	}

	public void setLast(Lexeme last) {
		this.last = last;
	}
}
