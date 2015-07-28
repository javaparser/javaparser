package me.tomassetti.symbolsolver.model.javaparser;

import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import me.tomassetti.symbolsolver.model.*;

import java.util.List;

/**
 * Created by federico on 28/07/15.
 */
public class ClassOrInterfaceDeclarationContext extends AbstractJavaParserContext<ClassOrInterfaceDeclaration> {

    public ClassOrInterfaceDeclarationContext(ClassOrInterfaceDeclaration wrappedNode) {
        super(wrappedNode);
    }

    @Override
    public SymbolReference solveSymbol(String name, TypeSolver typeSolver) {
        // first among declared fields
        for (BodyDeclaration member : wrappedNode.getMembers()){
            if (member instanceof FieldDeclaration) {
                SymbolDeclarator symbolDeclarator = JavaParserFactory.getSymbolDeclarator(member);
                SymbolReference ref = solveWith(symbolDeclarator, name);
                if (ref.isSolved()) {
                    return ref;
                }
            }
        }
        // then among inherited fields
        // TODO
        // then to parent
        return getParent().solveSymbol(name, typeSolver);
    }

    @Override
    public MethodReference solveMethod(String name, List<TypeReference> parameterTypes, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }
}
