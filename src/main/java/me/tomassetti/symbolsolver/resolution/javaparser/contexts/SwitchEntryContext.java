package me.tomassetti.symbolsolver.resolution.javaparser.contexts;

import com.github.javaparser.ast.stmt.SwitchEntryStmt;
import com.github.javaparser.ast.stmt.SwitchStmt;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.typesystem.ReferenceTypeUsage;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import me.tomassetti.symbolsolver.resolution.SymbolReference;
import me.tomassetti.symbolsolver.resolution.TypeSolver;
import me.tomassetti.symbolsolver.resolution.javaparser.JavaParserFacade;

import java.util.List;

/**
 * Created by federico on 24/08/15.
 */
public class SwitchEntryContext extends AbstractJavaParserContext<SwitchEntryStmt> {

    public SwitchEntryContext(SwitchEntryStmt wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }


    @Override
    public SymbolReference<? extends ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        SwitchStmt switchStmt = (SwitchStmt) wrappedNode.getParentNode();
        TypeUsage type = JavaParserFacade.get(typeSolver).getType(switchStmt.getSelector());
        if (type.isReferenceType() && type.asReferenceTypeUsage().isEnum()) {
            if (type instanceof ReferenceTypeUsage) {
                ReferenceTypeUsage typeUsageOfTypeDeclaration = (ReferenceTypeUsage) type;
                if (typeUsageOfTypeDeclaration.getTypeDeclaration().hasField(name)) {
                    return SymbolReference.solved(typeUsageOfTypeDeclaration.getTypeDeclaration().getField(name));
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
