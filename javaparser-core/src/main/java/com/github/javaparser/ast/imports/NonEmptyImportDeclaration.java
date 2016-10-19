package com.github.javaparser.ast.imports;

import com.github.javaparser.Range;

/**
 * Common ancestor for all imports, aside EmptyImportDeclaration
 */
public abstract class NonEmptyImportDeclaration extends ImportDeclaration {

    protected NonEmptyImportDeclaration(Range range) {
        super(range);
    }

    abstract boolean isAsterisk();

    abstract boolean isStatic();
}
