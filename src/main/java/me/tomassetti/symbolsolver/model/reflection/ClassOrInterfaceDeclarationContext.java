package me.tomassetti.symbolsolver.model.reflection;

import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import me.tomassetti.symbolsolver.model.*;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.javaparser.JavaParserFactory;
import me.tomassetti.symbolsolver.model.javaparser.UnsolvedTypeException;
import me.tomassetti.symbolsolver.model.javaparser.contexts.AbstractJavaParserContext;
import me.tomassetti.symbolsolver.model.javaparser.declarations.JavaParserClassDeclaration;
import me.tomassetti.symbolsolver.model.javaparser.declarations.JavaParserTypeVariableDeclaration;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;

import java.util.List;
import java.util.Optional;

/**
 * Created by federico on 28/07/15.
 */
public class ClassOrInterfaceDeclarationContext implements Context {

    private Class<?> wrapped;

    public ClassOrInterfaceDeclarationContext(Class<?> clazz) {
        this.wrapped = clazz;
    }


    @Override
    public SymbolReference<ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }

    @Override
    public SymbolReference<TypeDeclaration> solveType(String name, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Context getParent() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isRoot() {
        throw new UnsupportedOperationException();
    }
}
