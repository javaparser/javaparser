package me.tomassetti.symbolsolver.model.javaparser;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.expr.QualifiedNameExpr;
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
    public SymbolReference<me.tomassetti.symbolsolver.model.TypeDeclaration> solveType(String name, TypeSolver typeSolver) {
        for (TypeDeclaration type : wrappedNode.getTypes()) {
            if (type.getName().equals(name)){
                if (type instanceof ClassOrInterfaceDeclaration) {
                    return SymbolReference.solved(new JavaParserClassDeclaration((ClassOrInterfaceDeclaration)type));
                } else {
                    throw new UnsupportedOperationException();
                }
            }
        }

        for (ImportDeclaration importDecl : wrappedNode.getImports()) {
            if (!importDecl.isStatic()) {
                if (!importDecl.isAsterisk()) {
                    System.out.println("IMPORT "+importDecl);
                    if (importDecl.getName() instanceof QualifiedNameExpr) {
                        String qName = importDecl.getName().toString();
                        SymbolReference<me.tomassetti.symbolsolver.model.TypeDeclaration> ref = typeSolver.tryToSolveType(qName);
                        if (ref.isSolved()) {
                            return ref;
                        }
                    } else {
                        throw new UnsupportedOperationException();
                    }
                }
            }

        }

        // TODO look in current package


        // TODO DO NOT look for absolute name if this name is not qualified: you cannot import classes from the default package

        return typeSolver.tryToSolveType(name);
    }

    @Override
    public MethodReference solveMethod(String name, List<TypeReference> parameterTypes, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }
}
