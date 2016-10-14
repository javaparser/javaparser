package me.tomassetti.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.stmt.SwitchEntryStmt;
import com.github.javaparser.ast.stmt.SwitchStmt;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.usages.typesystem.ReferenceTypeImpl;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;
import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFacade;

import java.util.List;

public class SwitchEntryContext extends AbstractJavaParserContext<SwitchEntryStmt> {

    public SwitchEntryContext(SwitchEntryStmt wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public SymbolReference<? extends ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        SwitchStmt switchStmt = (SwitchStmt) wrappedNode.getParentNode();
        Type type = JavaParserFacade.get(typeSolver).getType(switchStmt.getSelector());
        if (type.isReferenceType() && type.asReferenceType().getTypeDeclaration().isEnum()) {
            if (type instanceof ReferenceTypeImpl) {
                ReferenceTypeImpl typeUsageOfTypeDeclaration = (ReferenceTypeImpl) type;
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
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<Type> parameterTypes, TypeSolver typeSolver) {
        return getParent().solveMethod(name, parameterTypes, typeSolver);
    }
}
