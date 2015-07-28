package me.tomassetti.symbolsolver.model.javaparser;

import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import me.tomassetti.symbolsolver.model.MethodReference;
import me.tomassetti.symbolsolver.model.SymbolReference;
import me.tomassetti.symbolsolver.model.TypeReference;
import me.tomassetti.symbolsolver.model.TypeSolver;

import java.util.List;

/**
 * Created by federico on 28/07/15.
 */
public class ClassOrInterfaceDeclarationContext extends AbstractJavaParserContext<ClassOrInterfaceDeclaration> {

    public ClassOrInterfaceDeclarationContext(ClassOrInterfaceDeclaration wrappedNode) {
        super(wrappedNode);
    }

    @Override
    public SymbolReference solveSymbol(String name, TypeSolver typeSolver) {
        // first among declared fields
        // then among inherited fields
        // then to parent
        throw new UnsupportedOperationException();
    }

    @Override
    public MethodReference solveMethod(String name, List<TypeReference> parameterTypes, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }
}
