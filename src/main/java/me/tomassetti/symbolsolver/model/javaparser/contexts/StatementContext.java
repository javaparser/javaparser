package me.tomassetti.symbolsolver.model.javaparser.contexts;

import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.Statement;
import me.tomassetti.symbolsolver.model.*;
import me.tomassetti.symbolsolver.model.MethodDeclaration;
import me.tomassetti.symbolsolver.model.TypeDeclaration;
import me.tomassetti.symbolsolver.model.javaparser.JavaParserFactory;
import me.tomassetti.symbolsolver.model.javaparser.UnsolvedSymbolException;

import java.util.List;

/**
 * Created by federico on 28/07/15.
 */
public class StatementContext extends AbstractJavaParserContext<Statement> {

    public StatementContext(Statement wrappedNode) {
        super(wrappedNode);
    }

    @Override
    public SymbolReference solveSymbol(String name, TypeSolver typeSolver) {
        // we should look in all the statements preceding, treating them as SymbolDeclarators
        if (wrappedNode.getParentNode() instanceof com.github.javaparser.ast.body.MethodDeclaration){
            return getParent().solveSymbol(name, typeSolver);
        }
        if (wrappedNode.getParentNode() instanceof LambdaExpr){
            throw new UnsupportedOperationException();
        }
        BlockStmt blockStmt = (BlockStmt)wrappedNode.getParentNode();
        int position = -1;
        for (int i=0; i<blockStmt.getStmts().size(); i++){
            if (blockStmt.getStmts().get(i).equals(wrappedNode)){
                position = i;
            }
        }
        if (position == -1){
            throw new RuntimeException();
        }
        for (int i = position-1; i>=0; i--){
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
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver) {
        return getParent().solveMethod(name, parameterTypes, typeSolver);
    }

    @Override
    public SymbolReference<TypeDeclaration> solveType(String name, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }
}
