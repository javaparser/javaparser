package me.tomassetti.symbolsolver.model.javaparser.contexts;

import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ForeachStmt;
import me.tomassetti.symbolsolver.model.SymbolReference;
import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.javaparser.declarations.JavaParserSymbolDeclaration;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;

import java.util.List;

/**
 * Created by federico on 23/08/15.
 */
public class ForechStatementContext extends AbstractJavaParserContext<ForeachStmt> {

    public ForechStatementContext(ForeachStmt wrappedNode) {
        super(wrappedNode);
    }

    @Override
    public SymbolReference<? extends ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        if (wrappedNode.getVariable().getVars().size() != 1) {
            throw new IllegalStateException();
        }
        VariableDeclarator variableDeclarator = wrappedNode.getVariable().getVars().get(0);
        if (variableDeclarator.getId().getName().equals(name)) {
            return SymbolReference.solved(JavaParserSymbolDeclaration.localVar(variableDeclarator, typeSolver));
        } else {
            if (wrappedNode.getParentNode() instanceof BlockStmt) {
                return StatementContext.solveInBlock(name, typeSolver, wrappedNode);
            } else {
                return getParent().solveSymbol(name, typeSolver);
            }
        }
    }

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver) {
        return getParent().solveMethod(name, parameterTypes, typeSolver);
    }
}
