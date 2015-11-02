package me.tomassetti.symbolsolver.resolution.javaparser.declarations;

import com.github.javaparser.ast.body.EnumDeclaration;
import me.tomassetti.symbolsolver.resolution.TypeSolver;

import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import me.tomassetti.symbolsolver.model.typesystem.ReferenceTypeUsage;

public class JavaParserEnumConstantDeclaration implements ValueDeclaration {

    private TypeSolver typeSolver;

    public JavaParserEnumConstantDeclaration(com.github.javaparser.ast.body.EnumConstantDeclaration wrappedNode, TypeSolver typeSolver) {
        this.wrappedNode = wrappedNode;
        this.typeSolver = typeSolver;
    }

    private com.github.javaparser.ast.body.EnumConstantDeclaration wrappedNode;

    @Override
    public TypeUsage getType() {
        return new ReferenceTypeUsage(new JavaParserEnumDeclaration((EnumDeclaration) wrappedNode.getParentNode(), typeSolver), typeSolver);
    }

    @Override
    public String getName() {
        return wrappedNode.getName();
    }

}
