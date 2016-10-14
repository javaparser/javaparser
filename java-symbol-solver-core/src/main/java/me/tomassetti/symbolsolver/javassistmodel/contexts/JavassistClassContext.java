package me.tomassetti.symbolsolver.javassistmodel.contexts;

import javassist.CtClass;
import javassist.bytecode.BadBytecode;
import javassist.bytecode.SignatureAttribute;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;
import me.tomassetti.symbolsolver.core.resolution.Context;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;

import java.util.List;
import java.util.Optional;

@Deprecated
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
    public Optional<Type> solveGenericType(String name, TypeSolver typeSolver) {
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
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<Type> parameterTypes, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Context getParent() {
        throw new UnsupportedOperationException();
    }

}
