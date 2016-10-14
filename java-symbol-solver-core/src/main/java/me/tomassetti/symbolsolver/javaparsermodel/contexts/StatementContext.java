package me.tomassetti.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.IfStmt;
import com.github.javaparser.ast.stmt.Statement;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.core.resolution.Context;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.resolution.Value;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;
import me.tomassetti.symbolsolver.resolution.*;
import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFactory;

import java.util.List;
import java.util.Optional;

public class StatementContext<N extends Statement> extends AbstractJavaParserContext<N> {

    public StatementContext(N wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    public static SymbolReference<? extends ValueDeclaration> solveInBlock(String name, TypeSolver typeSolver, Statement stmt) {
        if (!(stmt.getParentNode() instanceof BlockStmt)) {
            throw new IllegalArgumentException();
        }
        BlockStmt blockStmt = (BlockStmt) stmt.getParentNode();
        int position = -1;
        for (int i = 0; i < blockStmt.getStmts().size(); i++) {
            if (blockStmt.getStmts().get(i).equals(stmt)) {
                position = i;
            }
        }
        if (position == -1) {
            throw new RuntimeException();
        }
        for (int i = position - 1; i >= 0; i--) {
            SymbolDeclarator symbolDeclarator = JavaParserFactory.getSymbolDeclarator(blockStmt.getStmts().get(i), typeSolver);
            SymbolReference symbolReference = solveWith(symbolDeclarator, name);
            if (symbolReference.isSolved()) {
                return symbolReference;
            }
        }

        // if nothing is found we should ask the parent context
        return JavaParserFactory.getContext(stmt.getParentNode(), typeSolver).solveSymbol(name, typeSolver);
    }

    @Override
    public Optional<Value> solveSymbolAsValue(String name, TypeSolver typeSolver) {
        // we should look in all the statements preceding, treating them as SymbolDeclarators
        if (wrappedNode.getParentNode() instanceof com.github.javaparser.ast.body.MethodDeclaration) {
            return getParent().solveSymbolAsValue(name, typeSolver);
        }
        if (wrappedNode.getParentNode() instanceof LambdaExpr) {
            return getParent().solveSymbolAsValue(name, typeSolver);
        }
        if (wrappedNode.getParentNode() instanceof IfStmt) {
            return getParent().solveSymbolAsValue(name, typeSolver);
        }
        if (!(wrappedNode.getParentNode() instanceof BlockStmt)) {
            return getParent().solveSymbolAsValue(name, typeSolver);
        }
        BlockStmt blockStmt = (BlockStmt) wrappedNode.getParentNode();
        int position = -1;
        for (int i = 0; i < blockStmt.getStmts().size(); i++) {
            if (blockStmt.getStmts().get(i).equals(wrappedNode)) {
                position = i;
            }
        }
        if (position == -1) {
            throw new RuntimeException();
        }
        for (int i = position - 1; i >= 0; i--) {
            SymbolDeclarator symbolDeclarator = JavaParserFactory.getSymbolDeclarator(blockStmt.getStmts().get(i), typeSolver);
            Optional<Value> symbolReference = solveWithAsValue(symbolDeclarator, name, typeSolver);
            if (symbolReference.isPresent()) {
                return symbolReference;
            }
        }

        // if nothing is found we should ask the parent context
        Context parentContext = getParent();
        return parentContext.solveSymbolAsValue(name, typeSolver);
    }

    @Override
    public SymbolReference<? extends ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        // we should look in all the statements preceding, treating them as SymbolDeclarators
        if (wrappedNode.getParentNode() instanceof com.github.javaparser.ast.body.MethodDeclaration) {
            return getParent().solveSymbol(name, typeSolver);
        }
        if (wrappedNode.getParentNode() instanceof com.github.javaparser.ast.body.ConstructorDeclaration) {
            return getParent().solveSymbol(name, typeSolver);
        }
        if (wrappedNode.getParentNode() instanceof LambdaExpr) {
            return getParent().solveSymbol(name, typeSolver);
        }
        if (!(wrappedNode.getParentNode() instanceof BlockStmt)) {
            return getParent().solveSymbol(name, typeSolver);
        }
        BlockStmt blockStmt = (BlockStmt) wrappedNode.getParentNode();
        int position = -1;
        for (int i = 0; i < blockStmt.getStmts().size(); i++) {
            if (blockStmt.getStmts().get(i).equals(wrappedNode)) {
                position = i;
            }
        }
        if (position == -1) {
            throw new RuntimeException();
        }
        for (int i = position - 1; i >= 0; i--) {
            SymbolDeclarator symbolDeclarator = JavaParserFactory.getSymbolDeclarator(blockStmt.getStmts().get(i), typeSolver);
            SymbolReference symbolReference = solveWith(symbolDeclarator, name);
            if (symbolReference.isSolved()) {
                return symbolReference;
            }
        }

        // if nothing is found we should ask the parent context
        return getParent().solveSymbol(name, typeSolver);
    }

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<Type> parameterTypes, TypeSolver typeSolver) {
        return getParent().solveMethod(name, parameterTypes, typeSolver);
    }

    @Override
    public SymbolReference<TypeDeclaration> solveType(String name, TypeSolver typeSolver) {
        return getParent().solveType(name, typeSolver);
    }
}
