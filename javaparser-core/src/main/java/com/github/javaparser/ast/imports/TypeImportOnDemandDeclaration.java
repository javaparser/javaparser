package com.github.javaparser.ast.imports;

import com.github.javaparser.Range;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import static com.github.javaparser.ast.expr.NameExpr.*;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * Examples: 
 * <code>
 *     import com.github.javaparser.*;
 *     import com.github.javaparser.JavaParser.*;
 * </code>
 * Since a parser cannot differentiate between a type name and a package name, we simply store a NameExpr.
 * <p><a href="https://docs.oracle.com/javase/specs/jls/se8/html/jls-7.html#jls-7.5.2">JLS 7.5.2. Type-Import-on-Demand Declarations</a></p>
 */
public class TypeImportOnDemandDeclaration extends ImportDeclaration {
    private NameExpr name;

    public TypeImportOnDemandDeclaration() {
        this(Range.UNKNOWN, name("empty"));
    }
    
    public TypeImportOnDemandDeclaration(Range range, NameExpr name) {
        super(range);
        setName(name);
    }
    
    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    /**
     * Retrieves the name of the import.
     *
     * @return the name of the import
     * @throws UnsupportedOperationException when invoked on an empty import declaration
     */
    public NameExpr getName() {
        return name;
    }

    /**
     * Sets the name this import.
     *
     * @param name
     *            the name to set
     */
    public ImportDeclaration setName(NameExpr name) {
        this.name = assertNotNull(name);
        setAsParentNodeOf(this.name);
        return this;
    }
}
