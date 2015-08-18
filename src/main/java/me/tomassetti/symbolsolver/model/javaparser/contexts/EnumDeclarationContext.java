package me.tomassetti.symbolsolver.model.javaparser.contexts;

import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import me.tomassetti.symbolsolver.model.*;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.javaparser.JavaParserFactory;
import me.tomassetti.symbolsolver.model.javaparser.UnsolvedTypeException;
import me.tomassetti.symbolsolver.model.javaparser.declarations.*;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;
import me.tomassetti.symbolsolver.model.usages.TypeUsageOfTypeParameter;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * @author Federico Tomassetti
 */
public class EnumDeclarationContext extends AbstractJavaParserContext<EnumDeclaration> {

    public EnumDeclarationContext(EnumDeclaration wrappedNode) {
        super(wrappedNode);
    }

    @Override
    public SymbolReference<ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        if (typeSolver == null) throw new IllegalArgumentException();

        // first among declared fields
        for (BodyDeclaration member : wrappedNode.getMembers()){
            if (member instanceof FieldDeclaration) {
                SymbolDeclarator symbolDeclarator = JavaParserFactory.getSymbolDeclarator(member, typeSolver);
                SymbolReference ref = solveWith(symbolDeclarator, name);
                if (ref.isSolved()) {
                    return ref;
                }
            }
        }

        // then to parent
        return getParent().solveSymbol(name, typeSolver);
    }

    @Override
    public Optional<Value> solveSymbolAsValue(String name, TypeSolver typeSolver) {
        if (typeSolver == null) throw new IllegalArgumentException();

        // first among declared fields
        for (BodyDeclaration member : wrappedNode.getMembers()){
            if (member instanceof FieldDeclaration) {
                SymbolDeclarator symbolDeclarator = JavaParserFactory.getSymbolDeclarator(member, typeSolver);
                Optional<Value> ref = solveWithAsValue(symbolDeclarator, name, typeSolver);
                if (ref.isPresent()) {
                    return ref;
                }
            }
        }

        // then to parent
        return getParent().solveSymbolAsValue(name, typeSolver);
    }

    @Override
    public Optional<TypeUsage> solveGenericType(String name, TypeSolver typeSolver) {
        return Optional.empty();
    }

    @Override
    public SymbolReference<TypeDeclaration> solveType(String name, TypeSolver typeSolver) {
        if (this.wrappedNode.getName().equals(name)){
            return SymbolReference.solved(new JavaParserEnumDeclaration(this.wrappedNode));
        }

        // Internal classes
        for (BodyDeclaration member : this.wrappedNode.getMembers()){
            if (member instanceof com.github.javaparser.ast.body.TypeDeclaration) {
                com.github.javaparser.ast.body.TypeDeclaration internalType = (com.github.javaparser.ast.body.TypeDeclaration) member;
                if (internalType.getName().equals(name)) {
                    if (internalType instanceof ClassOrInterfaceDeclaration) {
                        return SymbolReference.solved(new JavaParserClassDeclaration((ClassOrInterfaceDeclaration) internalType));
                    } else {
                        throw new UnsupportedOperationException();
                    }
                }
            }
        }

        return getParent().solveType(name, typeSolver);
    }

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver) {
        List<MethodDeclaration> candidateMethods = new ArrayList<>();
        for (BodyDeclaration member : this.wrappedNode.getMembers()) {
            if (member instanceof com.github.javaparser.ast.body.MethodDeclaration) {
                com.github.javaparser.ast.body.MethodDeclaration method = (com.github.javaparser.ast.body.MethodDeclaration)member;
                if (method.getName().equals(name)) {
                    candidateMethods.add(new JavaParserMethodDeclaration(method));
                }
            }
        }
        // TODO consider inherited methods
        return MethodResolutionLogic.findMostApplicable(candidateMethods, name, parameterTypes, typeSolver);
    }
}
