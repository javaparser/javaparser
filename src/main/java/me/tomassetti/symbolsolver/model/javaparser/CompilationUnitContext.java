package me.tomassetti.symbolsolver.model.javaparser;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import me.tomassetti.symbolsolver.model.*;

import java.util.List;

/**
 * Created by federico on 30/07/15.
 */
public class CompilationUnitContext extends AbstractJavaParserContext<CompilationUnit> {

    public CompilationUnitContext(CompilationUnit wrappedNode) {
        super(wrappedNode);
    }

    @Override
    public SymbolReference solveSymbol(String name, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }

    @Override
    public SymbolReference<ClassDeclaration> solveType(String name, TypeSolver typeSolver) {
        for (TypeDeclaration type : wrappedNode.getTypes()) {
            if (type.getName().equals(name)){
                if (type instanceof ClassOrInterfaceDeclaration) {
                    return SymbolReference.solved(new JavaParserClassDeclaration((ClassOrInterfaceDeclaration)type));
                } else {
                    throw new UnsupportedOperationException();
                }
            }
        }
        return typeSolver.tryToSolveType(name);
    }

    @Override
    public MethodReference solveMethod(String name, List<TypeReference> parameterTypes, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }
}
