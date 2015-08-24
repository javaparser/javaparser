package me.tomassetti.symbolsolver.model.javaparser.contexts;

import com.github.javaparser.ast.stmt.SwitchStmt;
import me.tomassetti.symbolsolver.JavaParserFacade;
import me.tomassetti.symbolsolver.model.SymbolReference;
import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.declarations.EnumDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;
import me.tomassetti.symbolsolver.model.usages.TypeUsageOfTypeDeclaration;

/**
 * Created by federico on 24/08/15.
 */
public class SwitchContext extends StatementContext<SwitchStmt> {

    public SwitchContext(SwitchStmt wrappedNode) {
        super(wrappedNode);
    }

    @Override
    public SymbolReference<? extends ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        TypeUsage typeUsage = JavaParserFacade.get(typeSolver).getType(wrappedNode.getSelector());
        if (typeUsage.isEnum()) {
            TypeUsageOfTypeDeclaration typeUsageOfTypeDeclaration = (TypeUsageOfTypeDeclaration)typeUsage;
            EnumDeclaration enumDeclaration = (EnumDeclaration)typeUsageOfTypeDeclaration.getTypeDeclaration();
            if (enumDeclaration.hasField(name, typeSolver)) {
                return SymbolReference.solved(enumDeclaration.getField(name, typeSolver));
            }
        }
        return super.solveSymbol(name, typeSolver);
    }

}
