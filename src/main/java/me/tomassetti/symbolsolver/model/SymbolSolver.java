package me.tomassetti.symbolsolver.model;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.ReferenceType;
import com.github.javaparser.ast.type.Type;
import me.tomassetti.symbolsolver.model.javaparser.JavaParserFactory;
import me.tomassetti.symbolsolver.model.javaparser.UnsolvedSymbolException;

import java.util.List;

/**
 * Created by federico on 28/07/15.
 */
public class SymbolSolver {

    private TypeSolver typeSolver;

    public SymbolSolver(TypeSolver typeSolver){
        if (typeSolver == null) throw new IllegalArgumentException();

        this.typeSolver = typeSolver;
    }

    public SymbolReference solveSymbol(String name, Context context) {
        return context.solveSymbol(name, typeSolver);
    }

    public SymbolReference solveSymbol(String name, Node node) {
        return solveSymbol(name, JavaParserFactory.getContext(node));
    }

    public SymbolReference<me.tomassetti.symbolsolver.model.TypeDeclaration> solveType(String name, Context context) {
        return context.solveType(name, typeSolver);
    }

    public SymbolReference<me.tomassetti.symbolsolver.model.TypeDeclaration> solveType(String name, Node node) {
        return solveType(name, JavaParserFactory.getContext(node));
    }

    public SymbolReference<MethodDeclaration> solveMethod(String methodName, List<TypeReference> params, Context context) {
        return context.solveMethod(methodName, params, typeSolver);
    }

    public SymbolReference<MethodDeclaration> solveMethod(String methodName, List<TypeReference> params, Node node) {
        return solveMethod(methodName, params, JavaParserFactory.getContext(node));
    }

    public me.tomassetti.symbolsolver.model.TypeDeclaration solveType(Type type) {
        if (type instanceof ReferenceType) {
            ReferenceType referenceType = (ReferenceType) type;
            // TODO consider array modifiers
            return solveType(referenceType.getType());
        } else if (type instanceof ClassOrInterfaceType) {
            ClassOrInterfaceType classType = (ClassOrInterfaceType) type;
            SymbolReference<SymbolDeclaration> ref = solveSymbol(classType.getName(), type);
            if (!ref.isSolved()) {
                throw new UnsolvedSymbolException(JavaParserFactory.getContext(type), classType.getName());
            }
            if (!(ref.getCorrespondingDeclaration().isType())) {
                throw new IllegalStateException();
            }
            return ref.getCorrespondingDeclaration().asTypeDeclaration();
        } else {
            throw new UnsupportedOperationException(type.getClass().getCanonicalName());
        }
    }
}
