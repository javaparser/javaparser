package me.tomassetti.symbolsolver.model.javaparser.declarations;

import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import me.tomassetti.symbolsolver.model.ClassDeclaration;
import me.tomassetti.symbolsolver.model.Context;
import me.tomassetti.symbolsolver.model.TypeDeclaration;
import me.tomassetti.symbolsolver.model.javaparser.JavaParserFactory;

/**
 * Created by federico on 30/07/15.
 */
public class JavaParserClassDeclaration implements ClassDeclaration {

    public JavaParserClassDeclaration(ClassOrInterfaceDeclaration wrappedNode) {
        this.wrappedNode = wrappedNode;
    }

    private ClassOrInterfaceDeclaration wrappedNode;

    @Override
    public Context getContext() {
        return JavaParserFactory.getContext(wrappedNode);
    }

    @Override
    public String getName() {
        return wrappedNode.getName();
    }

    @Override
    public boolean isField() {
        return false;
    }

    @Override
    public boolean isParameter() {
        return false;
    }

    @Override
    public boolean isType() {
        return true;
    }

    @Override
    public TypeDeclaration asTypeDeclaration() {
        return this;
    }

    @Override
    public TypeDeclaration getType() {
        throw new UnsupportedOperationException();
    }

    @Override
    public String getQualifiedName() {
        throw new UnsupportedOperationException();
    }
}
