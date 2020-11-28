package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.expr.InstanceOfExpr;
import com.github.javaparser.ast.expr.PatternExpr;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserPatternDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserSymbolDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * @author Roger Howell
 */
public class InstanceOfExprContext extends AbstractJavaParserContext<InstanceOfExpr> {

    public InstanceOfExprContext(InstanceOfExpr wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name) {
        Optional<PatternExpr> optionalPatternExpr = wrappedNode.getPattern();
        if(optionalPatternExpr.isPresent()) {
            if(optionalPatternExpr.get().getNameAsString().equals(name)) {
                JavaParserPatternDeclaration decl = JavaParserSymbolDeclaration.patternVar(optionalPatternExpr.get(), typeSolver);
                return SymbolReference.solved(decl);
            }
        }


        Optional<Context> optionalParentContext = getParent();
        if (!optionalParentContext.isPresent()) {
            return SymbolReference.unsolved(ResolvedValueDeclaration.class);
        }

        Context parentContext = optionalParentContext.get();
        if(parentContext instanceof BinaryExprContext) {
            Optional<PatternExpr> optionalPatternExpr1 = parentContext.patternExprInScope(name);
            if(optionalPatternExpr1.isPresent()) {
                JavaParserPatternDeclaration decl = JavaParserSymbolDeclaration.patternVar(optionalPatternExpr1.get(), typeSolver);
                return SymbolReference.solved(decl);
            }
        } // TODO: Also consider unary expr context


        // if nothing is found we should ask the parent context
        return solveSymbolInParentContext(name);
    }

    @Override
    public List<PatternExpr> patternExprsExposedFromChildren() {
        List<PatternExpr> results = new ArrayList<>();

        // If this instanceof expression has a pattern, add it to the list.
        wrappedNode.getPattern().ifPresent(results::add);

        return results;
    }



}
