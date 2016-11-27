package com.github.javaparser.ast.imports;

import com.github.javaparser.Range;
import com.github.javaparser.ast.observing.ObservableProperty;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * Example: <code>import com.github.javaparser.JavaParser;</code>
 * <p><a href="https://docs.oracle.com/javase/specs/jls/se8/html/jls-7.html#jls-7.5.1">JLS 7.5.1. Single-Type-Import Declarations</a></p>
 */
public class SingleTypeImportDeclaration extends NonEmptyImportDeclaration {
    private ClassOrInterfaceType type;

    public SingleTypeImportDeclaration() {
        this(null, new ClassOrInterfaceType());
    }

    public SingleTypeImportDeclaration(Range range, ClassOrInterfaceType type) {
        super(range);
        setType(type);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    public ClassOrInterfaceType getType() {
        return type;
    }

    public SingleTypeImportDeclaration setType(ClassOrInterfaceType type) {
        notifyPropertyChange(ObservableProperty.TYPE, this.type, type);
        this.type = assertNotNull(type);
        setAsParentNodeOf(type);
        return this;
    }

    @Override
    boolean isAsterisk() {
        return false;
    }

    @Override
    boolean isStatic() {
        return false;
    }
}
