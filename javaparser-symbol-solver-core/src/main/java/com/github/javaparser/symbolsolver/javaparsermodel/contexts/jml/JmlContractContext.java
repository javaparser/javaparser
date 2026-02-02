package com.github.javaparser.symbolsolver.javaparsermodel.contexts.jml;

import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.jml.clauses.JmlClause;
import com.github.javaparser.ast.jml.clauses.JmlContract;
import com.github.javaparser.ast.jml.clauses.JmlForallClause;
import com.github.javaparser.ast.jml.clauses.JmlOldClause;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.AbstractJavaParserContext;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserSymbolDeclaration;

/**
 * @author Alexander Weigl
 * @version 1 (02.07.22)
 */
public class JmlContractContext extends AbstractJavaParserContext<JmlContract> {
    public JmlContractContext(JmlContract wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name) {
        // Only old and forall clauses can introduce names in contracts!
        for (JmlClause clause : wrappedNode.getClauses()) {
            if (clause instanceof JmlForallClause) {
                JmlForallClause forall = (JmlForallClause) clause;
                for (Parameter variable : forall.getBoundedVariables()) {
                    if (name.equals(variable.getNameAsString())) {
                        return SymbolReference.solved(JavaParserSymbolDeclaration.parameter(variable, typeSolver));
                    }
                }
            }
            if (clause instanceof JmlOldClause) {
                JmlOldClause old = (JmlOldClause) clause;
                for (VariableDeclarator variable : old.getDeclarations().getVariables()) {
                    if (name.equals(variable.getNameAsString())) {
                        return SymbolReference.solved(JavaParserSymbolDeclaration.localVar(variable, typeSolver));
                    }
                }
            }
        }

        // Fallback to default implementation to find non-here defined names.
        return super.solveSymbol(name);
    }
}
