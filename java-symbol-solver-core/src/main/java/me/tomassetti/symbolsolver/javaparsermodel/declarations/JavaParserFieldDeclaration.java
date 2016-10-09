package me.tomassetti.symbolsolver.javaparsermodel.declarations;

import com.github.javaparser.ast.body.EnumConstantDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import me.tomassetti.symbolsolver.model.declarations.FieldDeclaration;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.typesystem.ReferenceTypeUsageImpl;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFacade;

public class JavaParserFieldDeclaration implements FieldDeclaration {

    private VariableDeclarator variableDeclarator;
    private com.github.javaparser.ast.body.FieldDeclaration wrappedNode;
    private EnumConstantDeclaration enumConstantDeclaration;
    private TypeSolver typeSolver;

    public JavaParserFieldDeclaration(VariableDeclarator variableDeclarator, TypeSolver typeSolver) {
        if (typeSolver == null) {
            throw new IllegalArgumentException("typeSolver should not be null");
        }
        this.variableDeclarator = variableDeclarator;
        this.typeSolver = typeSolver;
        if (!(variableDeclarator.getParentNode() instanceof com.github.javaparser.ast.body.FieldDeclaration)) {
            throw new IllegalStateException();
        }
        this.wrappedNode = (com.github.javaparser.ast.body.FieldDeclaration) variableDeclarator.getParentNode();
    }

    public JavaParserFieldDeclaration(EnumConstantDeclaration enumConstantDeclaration, TypeSolver typeSolver) {
        if (typeSolver == null) {
            throw new IllegalArgumentException("typeSolver should not be null");
        }
        this.enumConstantDeclaration = enumConstantDeclaration;
        this.typeSolver = typeSolver;
    }

    @Override
    public TypeUsage getType() {
        if (enumConstantDeclaration != null) {
            com.github.javaparser.ast.body.EnumDeclaration enumDeclaration = (com.github.javaparser.ast.body.EnumDeclaration) enumConstantDeclaration.getParentNode();
            return new ReferenceTypeUsageImpl(new JavaParserEnumDeclaration(enumDeclaration, typeSolver), typeSolver);
        } else {
            return JavaParserFacade.get(typeSolver).convert(wrappedNode.getType(), wrappedNode);
        }
    }

    @Override
    public String getName() {
        if (enumConstantDeclaration != null) {
            return enumConstantDeclaration.getName();
        } else {
            return variableDeclarator.getId().getName();
        }
    }

    @Override
    public boolean isField() {
        return true;
    }

	/**
	 * Returns the JavaParser node associated with this JavaParserFieldDeclaration.
	 *
	 * @return A visitable JavaParser node wrapped by this object.
	 */
	public com.github.javaparser.ast.body.FieldDeclaration getWrappedNode()
	{
		return wrappedNode;
	}

}
