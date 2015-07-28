package me.tomassetti.symbolsolver.model.javaparser;

import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.Statement;
import me.tomassetti.symbolsolver.model.*;

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
            SymbolDeclarator symbolDeclarator = JavaParserFactory.getSymbolDeclarator(blockStmt.getStmts().get(i));
            SymbolReference symbolReference = solveWith(symbolDeclarator, name);
            if (symbolReference.isSolved()) {
                return symbolReference;
            }
        }

        // if nothing is found we should ask the parent context
        return getParent().solveSymbol(name, typeSolver);
    }

    @Override
    public MethodReference solveMethod(String name, List<TypeReference> parameterTypes, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }

}
