package me.tomassetti.symbolsolver.model.javaparser;

import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.Statement;
import me.tomassetti.symbolsolver.model.*;

import java.util.List;

/**
 * Created by federico on 28/07/15.
 */
public class MethodContext extends AbstractJavaParserContext<com.github.javaparser.ast.body.MethodDeclaration> {


    public MethodContext(MethodDeclaration wrappedNode) {
        super(wrappedNode);
    }

    @Override
    public SymbolReference solveSymbol(String name, TypeSolver typeSolver) {
        for (Parameter parameter : wrappedNode.getParameters()) {
            SymbolDeclarator sb = JavaParserFactory.getSymbolDeclarator(parameter);
            SymbolReference symbolReference = solveWith(sb, name);
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
