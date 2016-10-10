package com.github.javaparser.ast.imports;

import com.github.javaparser.Range;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * A stray semicolon between the imports.
 * This isn't described in the JLS, but accepted by most or all tools that parse Java.
 */
public class EmptyImportDeclaration extends ImportDeclaration {
    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    public EmptyImportDeclaration() {
        this(Range.UNKNOWN);
    }

    public EmptyImportDeclaration(Range range) {
        super(range);
    }
}
