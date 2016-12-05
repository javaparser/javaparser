package com.github.javaparser.ast.imports;

import com.github.javaparser.Range;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * A stray semicolon between the imports.
 * This isn't described in the JLS, but accepted by most or all tools that parse Java.
 *
 * @deprecated will be removed in 3.0
 */
@Deprecated
public class EmptyImportDeclaration extends ImportDeclaration {

    public EmptyImportDeclaration() {
        this(null);
    }

    public EmptyImportDeclaration(Range range) {
        super(range);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }
}
