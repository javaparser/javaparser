package com.github.javaparser.junit.ast.visitor;

import com.github.javaparser.ast.visitor.GenericVisitorAdapter;
import com.github.javaparser.ast.visitor.ModifierVisitorAdapter;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;

/**
 * This class tests that all visitors implement all methods, even if the visitors are abstract, by making cnocrete subclasses of them.
 */

class GenericVisitorAdapterTest extends GenericVisitorAdapter<Object, Object> {
    // Has to be empty!
}

class VoidVisitorAdapterTest extends VoidVisitorAdapter<Object> {
    // Has to be empty!
}

class ModifierVisitorAdapterTest extends ModifierVisitorAdapter<Object> {
    // Has to be empty!
}