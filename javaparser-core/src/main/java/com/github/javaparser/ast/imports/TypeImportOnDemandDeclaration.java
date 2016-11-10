package com.github.javaparser.ast.imports;

import com.github.javaparser.Range;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithName;
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
 * Since a parser cannot differentiate between a type name and a package name, we can only store a Name.
 * <p><a href="https://docs.oracle.com/javase/specs/jls/se8/html/jls-7.html#jls-7.5.2">JLS 7.5.2. Type-Import-on-Demand Declarations</a></p>
 */
public class TypeImportOnDemandDeclaration extends NonEmptyImportDeclaration implements NodeWithName<TypeImportOnDemandDeclaration> {
    private Name name;

    public TypeImportOnDemandDeclaration() {
        this(Range.UNKNOWN, new Name());
    }
    
    public TypeImportOnDemandDeclaration(Range range, Name name) {
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
    @Override
    public Name getName() {
        return name;
    }

    /**
     * Sets the name this import.
     *
     * @param name
     *            the name to set
     */
    @Override
    public TypeImportOnDemandDeclaration setName(Name name) {
        this.name = assertNotNull(name);
        setAsParentNodeOf(this.name);
        return this;
    }

    @Override
    boolean isAsterisk() {
        return true;
    }

    @Override
    boolean isStatic() {
        return false;
    }
}
