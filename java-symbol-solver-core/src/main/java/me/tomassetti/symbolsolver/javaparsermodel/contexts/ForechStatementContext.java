package me.tomassetti.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ForeachStmt;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;
import me.tomassetti.symbolsolver.javaparsermodel.declarations.JavaParserSymbolDeclaration;

import java.util.List;

public class ForechStatementContext extends AbstractJavaParserContext<ForeachStmt> {

    public ForechStatementContext(ForeachStmt wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
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
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<Type> parameterTypes, TypeSolver typeSolver) {
        return getParent().solveMethod(name, parameterTypes, typeSolver);
    }
}
