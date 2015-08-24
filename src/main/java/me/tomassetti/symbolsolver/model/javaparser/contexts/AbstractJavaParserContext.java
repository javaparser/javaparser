package me.tomassetti.symbolsolver.model.javaparser.contexts;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.stmt.SwitchStmt;
import me.tomassetti.symbolsolver.model.*;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.javaparser.JavaParserFactory;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;

import java.util.Optional;

/**
 * @author Federico Tomassetti
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

    @Override
    public Optional<TypeUsage> solveGenericType(String name, TypeSolver typeSolver) {
        Context parent = getParent();
        if (parent == null) {
            return Optional.empty();
        } else {
            return parent.solveGenericType(name, typeSolver);
        }
    }

    public AbstractJavaParserContext(N wrappedNode) {
        if (wrappedNode ==  null) {
            throw new NullPointerException();
        }
        this.wrappedNode = wrappedNode;
    }

    protected static final SymbolReference<ValueDeclaration> solveWith(SymbolDeclarator symbolDeclarator, String name){
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
        if (wrappedNode.getParentNode() instanceof MethodCallExpr) {
            MethodCallExpr parentCall = (MethodCallExpr)wrappedNode.getParentNode();
            boolean found = false;
            if (parentCall.getArgs() != null) {
                for (Expression expression : parentCall.getArgs()) {
                    if (expression == wrappedNode) {
                        found = true;
                    }
                }
            }
            if (found) {
                return JavaParserFactory.getContext(wrappedNode.getParentNode().getParentNode());
            }
        }
        return JavaParserFactory.getContext(wrappedNode.getParentNode());
    }

}
