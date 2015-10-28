package me.tomassetti.symbolsolver.model.javaparser.contexts;

import com.github.javaparser.ast.stmt.SwitchEntryStmt;
import com.github.javaparser.ast.stmt.SwitchStmt;
import me.tomassetti.symbolsolver.JavaParserFacade;
import me.tomassetti.symbolsolver.model.SymbolReference;
import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import me.tomassetti.symbolsolver.model.typesystem.ReferenceTypeUsage;

import java.util.List;

/**
 * Created by federico on 24/08/15.
 */
public class SwitchEntryContext extends AbstractJavaParserContext<SwitchEntryStmt> {

    public SwitchEntryContext(SwitchEntryStmt wrappedNode) {
        super(wrappedNode);
    }


    @Override
    public SymbolReference<? extends ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        SwitchStmt switchStmt = (SwitchStmt) wrappedNode.getParentNode();
        TypeUsage type = JavaParserFacade.get(typeSolver).getType(switchStmt.getSelector());
        if (type.isEnum()) {
            if (type instanceof ReferenceTypeUsage) {
                ReferenceTypeUsage typeUsageOfTypeDeclaration = (ReferenceTypeUsage)type;
                if (typeUsageOfTypeDeclaration.getTypeDeclaration().hasField(name, typeSolver)) {
                    return SymbolReference.solved(typeUsageOfTypeDeclaration.getTypeDeclaration().getField(name, typeSolver));
                }
            } else {
                throw new UnsupportedOperationException();
            }
        }
        return getParent().solveSymbol(name, typeSolver);
    }

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver) {
        return getParent().solveMethod(name, parameterTypes, typeSolver);
    }
}
