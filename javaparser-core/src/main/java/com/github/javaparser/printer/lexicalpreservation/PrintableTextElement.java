package com.github.javaparser.printer.lexicalpreservation;

public interface PrintableTextElement {

	void accept(LexicalPreservingVisitor visitor);
}
