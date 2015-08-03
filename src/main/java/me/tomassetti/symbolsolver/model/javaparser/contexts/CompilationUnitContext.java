package me.tomassetti.symbolsolver.model.javaparser.contexts;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.expr.QualifiedNameExpr;
import me.tomassetti.symbolsolver.model.*;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.javaparser.declarations.JavaParserClassDeclaration;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;

import java.util.List;

/**
 * Created by federico on 30/07/15.
 */
public class CompilationUnitContext extends AbstractJavaParserContext<CompilationUnit> {

    public CompilationUnitContext(CompilationUnit wrappedNode) {
        super(wrappedNode);
    }

    @Override
    public SymbolReference<ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        return SymbolReference.unsolved(ValueDeclaration.class);
    }

    @Override
    public SymbolReference<me.tomassetti.symbolsolver.model.declarations.TypeDeclaration> solveType(String name, TypeSolver typeSolver) {
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
                    if (importDecl.getName() instanceof QualifiedNameExpr) {
                        String qName = importDecl.getName().toString();
                        if (qName.equals(name) || qName.endsWith("." + name)) {
                            SymbolReference<me.tomassetti.symbolsolver.model.declarations.TypeDeclaration> ref = typeSolver.tryToSolveType(qName);
                            if (ref.isSolved()) {
                                return ref;
                            }
                        }
                    } else {
                        throw new UnsupportedOperationException();
                    }
                }
            }

        }

        // Look in current package
        if (this.wrappedNode.getPackage() != null) {
            String qName = this.wrappedNode.getPackage().getName().toString() + "." + name;
            SymbolReference<me.tomassetti.symbolsolver.model.declarations.TypeDeclaration> ref = typeSolver.tryToSolveType(qName);
            if (ref.isSolved()) {
                return ref;
            }
        }

        // Look in the java.lang package
        SymbolReference<me.tomassetti.symbolsolver.model.declarations.TypeDeclaration> ref = typeSolver.tryToSolveType("java.lang."+name);
        if (ref.isSolved()) {
            return ref;
        }

        // DO NOT look for absolute name if this name is not qualified: you cannot import classes from the default package
        if (isQualifiedName(name)) {
            return typeSolver.tryToSolveType(name);
        } else {
            return SymbolReference.unsolved(me.tomassetti.symbolsolver.model.declarations.TypeDeclaration.class);
        }
    }

    private static boolean isQualifiedName(String name) {
        return name.contains(".");
    }

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }
}
