package me.tomassetti.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.body.*;
import me.tomassetti.symbolsolver.resolution.MethodResolutionLogic;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;
import me.tomassetti.symbolsolver.resolution.SymbolDeclarator;
import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFactory;
import me.tomassetti.symbolsolver.javaparsermodel.declarations.JavaParserClassDeclaration;
import me.tomassetti.symbolsolver.javaparsermodel.declarations.JavaParserEnumConstantDeclaration;
import me.tomassetti.symbolsolver.javaparsermodel.declarations.JavaParserEnumDeclaration;
import me.tomassetti.symbolsolver.javaparsermodel.declarations.JavaParserMethodDeclaration;

import java.util.ArrayList;
import java.util.List;

/**
 * @author Federico Tomassetti
 */
public class EnumDeclarationContext extends AbstractJavaParserContext<EnumDeclaration> {

    public EnumDeclarationContext(EnumDeclaration wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public SymbolReference<? extends ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        if (typeSolver == null) throw new IllegalArgumentException();

        // among constants
        for (EnumConstantDeclaration constant : wrappedNode.getEntries()) {
            if (constant.getName().equals(name)) {
                return SymbolReference.solved(new JavaParserEnumConstantDeclaration(constant, typeSolver));
            }
        }

        // among declared fields
        for (BodyDeclaration member : wrappedNode.getMembers()) {
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
    public SymbolReference<me.tomassetti.symbolsolver.model.declarations.TypeDeclaration> solveType(String name, TypeSolver typeSolver) {
        if (this.wrappedNode.getName().equals(name)) {
            return SymbolReference.solved(new JavaParserEnumDeclaration(this.wrappedNode, typeSolver));
        }

        // Internal classes
        for (BodyDeclaration member : this.wrappedNode.getMembers()) {
            if (member instanceof com.github.javaparser.ast.body.TypeDeclaration) {
                com.github.javaparser.ast.body.TypeDeclaration internalType = (com.github.javaparser.ast.body.TypeDeclaration) member;
                if (internalType.getName().equals(name)) {
                    if (internalType instanceof ClassOrInterfaceDeclaration) {
                        return SymbolReference.solved(new JavaParserClassDeclaration((ClassOrInterfaceDeclaration) internalType, typeSolver));
                    } else {
                        throw new UnsupportedOperationException();
                    }
                }
            }
        }

        return getParent().solveType(name, typeSolver);
    }

    @Override
    public SymbolReference<me.tomassetti.symbolsolver.model.declarations.MethodDeclaration> solveMethod(String name, List<Type> parameterTypes, TypeSolver typeSolver) {
        List<me.tomassetti.symbolsolver.model.declarations.MethodDeclaration> candidateMethods = new ArrayList<>();
        for (BodyDeclaration member : this.wrappedNode.getMembers()) {
            if (member instanceof com.github.javaparser.ast.body.MethodDeclaration) {
                com.github.javaparser.ast.body.MethodDeclaration method = (com.github.javaparser.ast.body.MethodDeclaration) member;
                if (method.getName().equals(name)) {
                    candidateMethods.add(new JavaParserMethodDeclaration(method, typeSolver));
                }
            }
        }
        // TODO consider inherited methods
        return MethodResolutionLogic.findMostApplicable(candidateMethods, name, parameterTypes, typeSolver);
    }
}
