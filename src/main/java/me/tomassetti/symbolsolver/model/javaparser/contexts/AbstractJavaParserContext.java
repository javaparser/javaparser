package me.tomassetti.symbolsolver.model.javaparser.contexts;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import me.tomassetti.symbolsolver.model.*;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.javaparser.JavaParserFactory;

/**
 * Created by federico on 28/07/15.
 */
public abstract class AbstractJavaParserContext<N extends Node> implements Context {

    protected N wrappedNode;

    public AbstractJavaParserContext(N wrappedNode) {
        this.wrappedNode = wrappedNode;
    }

    protected final SymbolReference solveWith(SymbolDeclarator symbolDeclarator, String name){
        for (ValueDeclaration decl : symbolDeclarator.getSymbolDeclarations()){
            if (decl.getName().equals(name)){
                return SymbolReference.solved(decl);
            }
        }
        return SymbolReference.unsolved(ValueDeclaration.class);
    }

    @Override
    public final Context getParent() {
        return JavaParserFactory.getContext(wrappedNode.getParentNode());
    }

    @Override
    public final boolean isRoot() {
        return (wrappedNode instanceof CompilationUnit);
    }
}
