package me.tomassetti.symbolsolver.model.javaparser.contexts;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import me.tomassetti.symbolsolver.model.*;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.javaparser.JavaParserFactory;

import java.util.Optional;

/**
 * Created by federico on 28/07/15.
 */
public abstract class AbstractJavaParserContext<N extends Node> implements Context {

    protected N wrappedNode;

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        AbstractJavaParserContext that = (AbstractJavaParserContext) o;

        if (wrappedNode != null ? !wrappedNode.equals(that.wrappedNode) : that.wrappedNode != null) return false;

        return true;
    }

    @Override
    public int hashCode() {
        return wrappedNode != null ? wrappedNode.hashCode() : 0;
    }

    public AbstractJavaParserContext(N wrappedNode) {
        this.wrappedNode = wrappedNode;
    }

    protected final SymbolReference<ValueDeclaration> solveWith(SymbolDeclarator symbolDeclarator, String name){
        for (ValueDeclaration decl : symbolDeclarator.getSymbolDeclarations()){
            if (decl.getName().equals(name)){
                return SymbolReference.solved(decl);
            }
        }
        return SymbolReference.unsolved(ValueDeclaration.class);
    }

    protected Optional<Value> solveWithAsValue(SymbolDeclarator symbolDeclarator, String name, TypeSolver typeSolver){
        for (ValueDeclaration decl : symbolDeclarator.getSymbolDeclarations()){
            if (decl.getName().equals(name)){
                return Optional.of(Value.from(decl, typeSolver));
            }
        }
        return Optional.empty();
    }

    @Override
    public final Context getParent() {
        return JavaParserFactory.getContext(wrappedNode.getParentNode());
    }

}
