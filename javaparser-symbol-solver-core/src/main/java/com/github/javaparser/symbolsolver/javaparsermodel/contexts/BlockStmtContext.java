package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

import java.util.List;

public class BlockStmtContext extends AbstractJavaParserContext<BlockStmt> {


    public BlockStmtContext(BlockStmt wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }

    @Override
    public SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> argumentsTypes, boolean staticOnly, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<VariableDeclarator> localVariablesExposedToChild(Node child) {
        throw new UnsupportedOperationException();
    }
}
