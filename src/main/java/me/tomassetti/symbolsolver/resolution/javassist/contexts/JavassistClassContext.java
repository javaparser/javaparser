package me.tomassetti.symbolsolver.resolution.javassist.contexts;

import javassist.CtClass;
import javassist.bytecode.BadBytecode;
import javassist.bytecode.SignatureAttribute;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import me.tomassetti.symbolsolver.resolution.Context;
import me.tomassetti.symbolsolver.resolution.SymbolReference;
import me.tomassetti.symbolsolver.resolution.TypeSolver;

import java.util.List;
import java.util.Optional;

/**
 * Created by fede on 8/14/15.
 */
public class JavassistClassContext implements Context {

    private CtClass wrappedNode;

    public JavassistClassContext(CtClass wrappedNode) {
        this.wrappedNode = wrappedNode;
    }

    @Override
    public SymbolReference<ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }

    @Override
    public SymbolReference<TypeDeclaration> solveType(String name, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Optional<TypeUsage> solveGenericType(String name, TypeSolver typeSolver) {
        try {
            if (wrappedNode.getGenericSignature() != null) {
                SignatureAttribute.ClassSignature classSignature = SignatureAttribute.toClassSignature(wrappedNode.getGenericSignature());
                for (SignatureAttribute.TypeParameter tp : classSignature.getParameters()) {
                    if (tp.getName().equals(name)) {
                        throw new UnsupportedOperationException();
                        //OK, ora bisognerebbe capire come prendere il valore corrispondente
                    }
                }
            }
        } catch (BadBytecode bb) {
            throw new RuntimeException(bb);
        }
        return Optional.empty();
        //throw new UnsupportedOperationException("TO be implemented");
    }

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Context getParent() {
        throw new UnsupportedOperationException();
    }

}
