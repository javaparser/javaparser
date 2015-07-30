package me.tomassetti.symbolsolver.model.javaparser;

import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import me.tomassetti.symbolsolver.model.ClassDeclaration;
import me.tomassetti.symbolsolver.model.Context;

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
}
