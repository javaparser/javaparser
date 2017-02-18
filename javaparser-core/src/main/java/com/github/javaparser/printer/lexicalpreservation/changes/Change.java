package com.github.javaparser.printer.lexicalpreservation.changes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.printer.concretesyntaxmodel.CsmConditional;

public interface Change {

    boolean evaluate(CsmConditional csmConditional, Node node);
}
