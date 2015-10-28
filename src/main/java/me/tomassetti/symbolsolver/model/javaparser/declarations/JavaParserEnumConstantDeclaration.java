package me.tomassetti.symbolsolver.model.javaparser.declarations;

import com.github.javaparser.ast.body.EnumDeclaration;
import me.tomassetti.symbolsolver.model.TypeSolver;

import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import me.tomassetti.symbolsolver.model.typesystem.ReferenceTypeUsage;

/**
 * Created by federico on 21/08/15.
 */
public class JavaParserEnumConstantDeclaration implements ValueDeclaration {

    public JavaParserEnumConstantDeclaration(com.github.javaparser.ast.body.EnumConstantDeclaration wrappedNode) {
        this.wrappedNode = wrappedNode;
    }

    private com.github.javaparser.ast.body.EnumConstantDeclaration wrappedNode;

    @Override
    public TypeUsage getType(TypeSolver typeSolver) {
        return new ReferenceTypeUsage(new JavaParserEnumDeclaration((EnumDeclaration) wrappedNode.getParentNode()));
    }

    @Override
    public String getName() {
        return wrappedNode.getName();
    }

}
