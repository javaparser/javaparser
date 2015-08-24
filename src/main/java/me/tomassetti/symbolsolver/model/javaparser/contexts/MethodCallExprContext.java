package me.tomassetti.symbolsolver.model.javaparser.contexts;

import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import me.tomassetti.symbolsolver.JavaParserFacade;
import me.tomassetti.symbolsolver.model.*;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.javaparser.JavaParserFactory;
import me.tomassetti.symbolsolver.model.javaparser.UnsolvedSymbolException;
import me.tomassetti.symbolsolver.model.usages.MethodUsage;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;

import java.util.List;
import java.util.Optional;

/**
 * Created by federico on 31/07/15.
 */
public class MethodCallExprContext extends AbstractJavaParserContext<MethodCallExpr> {

    public MethodCallExprContext(MethodCallExpr wrappedNode) {
        super(wrappedNode);
    }

    @Override
    public Optional<TypeUsage> solveGenericType(String name, TypeSolver typeSolver) {
        if (wrappedNode.getTypeArgs() != null) {
            throw new UnsupportedOperationException(name);
        }
        TypeUsage typeOfScope = JavaParserFacade.get(typeSolver).getType(wrappedNode.getScope());
        return typeOfScope.solveGenericType(name);
    }

    @Override
    public Optional<MethodUsage> solveMethodAsUsage(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver) {
        // TODO consider call of static methods
        if (wrappedNode.getScope() != null) {
            try {
                TypeUsage typeOfScope = JavaParserFacade.get(typeSolver).getType(wrappedNode.getScope());
                return typeOfScope.solveMethodAsUsage(name, parameterTypes, typeSolver, this);
            } catch (UnsolvedSymbolException e){
                // ok, maybe it was instead a static access, so let's look for a type
                if (wrappedNode.getScope() instanceof NameExpr){
                    String className = ((NameExpr)wrappedNode.getScope()).getName();
                    SymbolReference<TypeDeclaration> ref = solveType(className, typeSolver);
                    if (ref.isSolved()) {
                        SymbolReference<MethodDeclaration> m = ref.getCorrespondingDeclaration().solveMethod(name, parameterTypes, typeSolver);
                        if (m.isSolved()) {
                            return Optional.of(new MethodUsage(m.getCorrespondingDeclaration(), typeSolver));
                        } else {
                            throw new UnsolvedSymbolException(ref.getCorrespondingDeclaration().toString(), "Method "+name+" with parameterTypes "+parameterTypes);
                        }
                    } else {
                        throw e;
                    }
                } else {
                    throw e;
                }
            }
        } else {
            if (wrappedNode.getParentNode() instanceof MethodCallExpr) {
                MethodCallExpr parent = (MethodCallExpr)wrappedNode.getParentNode();
                if (parent.getScope() == wrappedNode) {
                    return getParent().getParent().solveMethodAsUsage(name, parameterTypes, typeSolver);
                }
            }
            //TypeUsage typeOfScope = JavaParserFacade.get(typeSolver).getTypeOfThisIn(wrappedNode);
            //return typeOfScope.solveMethodAsUsage(name, parameterTypes, typeSolver, this);
            Context parentContext = getParent();
            //System.out.println("NAME "+name);
            return parentContext.solveMethodAsUsage(name, parameterTypes, typeSolver);
        }
    }

    @Override
    public SymbolReference<? extends ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        return getParent().solveSymbol(name, typeSolver);
    }

    @Override
    public Optional<Value> solveSymbolAsValue(String name, TypeSolver typeSolver) {
        return getParent().solveSymbolAsValue(name, typeSolver);
    }

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver) {
        if (wrappedNode.getScope() != null) {
            TypeUsage typeOfScope = JavaParserFacade.get(typeSolver).getType(wrappedNode.getScope());
            return typeOfScope.solveMethod(name, parameterTypes, typeSolver);
        } else {
            TypeUsage typeOfScope = JavaParserFacade.get(typeSolver).getTypeOfThisIn(wrappedNode);
            return typeOfScope.solveMethod(name, parameterTypes, typeSolver);
        }
    }
}
