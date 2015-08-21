package me.tomassetti.symbolsolver.model.javaparser.declarations;

import com.github.javaparser.ast.body.EnumDeclaration;
import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;

/**
 * Created by federico on 21/08/15.
 */
public class JavaParserEnumConstantDeclaration implements ValueDeclaration {

    public JavaParserEnumConstantDeclaration(com.github.javaparser.ast.body.EnumConstantDeclaration wrappedNode) {
        this.wrappedNode = wrappedNode;
    }

    private com.github.javaparser.ast.body.EnumConstantDeclaration wrappedNode;

    @Override
    public TypeDeclaration getType(TypeSolver typeSolver) {
        return new JavaParserEnumDeclaration((EnumDeclaration) wrappedNode.getParentNode());
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
    public boolean isVariable() {
        return false;
    }

    @Override
    public boolean isType() {
        return false;
    }

}
