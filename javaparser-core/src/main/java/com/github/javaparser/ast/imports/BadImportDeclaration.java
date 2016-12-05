package com.github.javaparser.ast.imports;

import com.github.javaparser.Range;
import com.github.javaparser.ast.nodeTypes.BadNode;
import com.github.javaparser.ast.observing.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * An import declaration that failed to parse.
 */
public class BadImportDeclaration extends ImportDeclaration implements
        BadNode<BadImportDeclaration> {

    private String sourceText;

    public BadImportDeclaration() {
        this(null, "import ???;");
    }

    public BadImportDeclaration(Range range, String sourceText) {
        super(range);
        setSourceText(sourceText);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    @Override
    public String getSourceText() {
        return sourceText;
    }

    @Override
    public BadImportDeclaration setSourceText(String sourceText) {
        notifyPropertyChange(ObservableProperty.SOURCE_TEXT, this.sourceText, sourceText);
        this.sourceText = assertNotNull(sourceText);
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
