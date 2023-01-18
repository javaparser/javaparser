package com.github.javaparser.printer.lexicalpreservation;

import java.io.StringWriter;

public class LexicalPreservingVisitor {

	private StringWriter writer;
	
	public LexicalPreservingVisitor() {
		this(new StringWriter());
	}
	
	public LexicalPreservingVisitor(StringWriter writer) {
		this.writer = writer;
	}

	public void visit(ChildTextElement child) {
		child.accept(this);
	}
	
	public void visit(TokenTextElement token) {
		writer.append(token.getText());
	}
	
	@Override
	public String toString() {
		return writer.toString();
	}
}
