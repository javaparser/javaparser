package com.github.javaparser.ast.imports;

import com.github.javaparser.Range;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * Example: <code>import static com.github.javaparser.JavaParser.parse;</code>
 * In the example, "com.github.javaparser.JavaParser" is the type,
 * and "parse" is the staticMember.
 * <p><a href="https://docs.oracle.com/javase/specs/jls/se8/html/jls-7.html#jls-7.5.3">7.5.3. Single-Static-Import Declarations</a></p>
 */
public class SingleStaticImportDeclaration extends NonEmptyImportDeclaration {
    private ClassOrInterfaceType type;
    private String staticMember;

    public SingleStaticImportDeclaration() {
        this(Range.UNKNOWN, new ClassOrInterfaceType(), "empty");
    }

    public SingleStaticImportDeclaration(Range range, ClassOrInterfaceType type, String staticMember) {
        super(range);
        setType(type);
        setStaticMember(staticMember);
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

    public SingleStaticImportDeclaration setType(ClassOrInterfaceType type) {
        this.type = assertNotNull(type);
        setAsParentNodeOf(type);
        return this;
    }

    public String getStaticMember() {
        return staticMember;
    }

    public SingleStaticImportDeclaration setStaticMember(String staticMember) {
        this.staticMember = assertNotNull(staticMember);
        return this;
    }

    @Override
    boolean isAsterisk() {
        return false;
    }

    @Override
    boolean isStatic() {
        return true;
    }
}
