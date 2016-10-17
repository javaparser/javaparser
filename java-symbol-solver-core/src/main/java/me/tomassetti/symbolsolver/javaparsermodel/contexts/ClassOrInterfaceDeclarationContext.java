package me.tomassetti.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFactory;
import me.tomassetti.symbolsolver.javaparsermodel.UnsolvedSymbolException;
import me.tomassetti.symbolsolver.javaparsermodel.declarations.JavaParserClassDeclaration;
import me.tomassetti.symbolsolver.javaparsermodel.declarations.JavaParserInterfaceDeclaration;
import me.tomassetti.symbolsolver.javaparsermodel.declarations.JavaParserMethodDeclaration;
import me.tomassetti.symbolsolver.javaparsermodel.declarations.JavaParserTypeParameter;
import me.tomassetti.symbolsolver.model.declarations.AccessLevel;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.resolution.Value;
import me.tomassetti.symbolsolver.model.usages.typesystem.ReferenceType;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;
import me.tomassetti.symbolsolver.model.usages.typesystem.TypeParameter;
import me.tomassetti.symbolsolver.resolution.MethodResolutionLogic;
import me.tomassetti.symbolsolver.resolution.SymbolDeclarator;
import me.tomassetti.symbolsolver.resolution.SymbolSolver;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * @author Federico Tomassetti
 */
public class ClassOrInterfaceDeclarationContext extends AbstractJavaParserContext<ClassOrInterfaceDeclaration> {

    public ClassOrInterfaceDeclarationContext(ClassOrInterfaceDeclaration wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public SymbolReference<? extends ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        if (typeSolver == null) throw new IllegalArgumentException();

        // first among declared fields
        for (BodyDeclaration member : wrappedNode.getMembers()) {
            if (member instanceof FieldDeclaration) {
                SymbolDeclarator symbolDeclarator = JavaParserFactory.getSymbolDeclarator(member, typeSolver);
                SymbolReference ref = solveWith(symbolDeclarator, name);
                if (ref.isSolved()) {
                    return ref;
                }
            }
        }

        // then among inherited fields
        for (ReferenceType ancestor : getDeclaration().getAncestors()) {
            SymbolReference ref = new SymbolSolver(typeSolver).solveSymbolInType(ancestor.getTypeDeclaration(), name);
            if (ref.isSolved() && ref.getCorrespondingDeclaration().asField().accessLevel() != AccessLevel.PRIVATE) {
                return ref;
            }
        }

        // then to parent
        return getParent().solveSymbol(name, typeSolver);
    }

    @Override
    public Optional<Value> solveSymbolAsValue(String name, TypeSolver typeSolver) {
        if (typeSolver == null) throw new IllegalArgumentException();

        // first among declared fields
        for (BodyDeclaration member : wrappedNode.getMembers()) {
            if (member instanceof FieldDeclaration) {
                SymbolDeclarator symbolDeclarator = JavaParserFactory.getSymbolDeclarator(member, typeSolver);
                Optional<Value> ref = solveWithAsValue(symbolDeclarator, name, typeSolver);
                if (ref.isPresent()) {
                    return ref;
                }
            }
        }

        // then among inherited fields
        for (ReferenceType ancestor : getDeclaration().getAncestors()) {
            Optional<Value> ref = ContextHelper.getContext(ancestor.getTypeDeclaration()).solveSymbolAsValue(name, typeSolver);
            if (ref.isPresent()) {
                return ref;
            }
        }

        // then to parent
        return getParent().solveSymbolAsValue(name, typeSolver);
    }

    @Override
    public Optional<Type> solveGenericType(String name, TypeSolver typeSolver) {
        for (com.github.javaparser.ast.TypeParameter tp : wrappedNode.getTypeParameters()) {
            if (tp.getName().equals(name)) {
                return Optional.of(new TypeParameter(new JavaParserTypeParameter(tp, typeSolver)));
            }
        }
        return getParent().solveGenericType(name, typeSolver);
    }

    @Override
    public SymbolReference<TypeDeclaration> solveType(String name, TypeSolver typeSolver) {
        SymbolReference<TypeDeclaration> ref = new SymbolSolver(typeSolver).solveTypeInType(getDeclaration(), name);
        if (ref.isSolved()) {
            return ref;
        }
        return getParent().solveType(name, typeSolver);
    }

    private TypeDeclaration getDeclaration() {
        if (this.wrappedNode.isInterface()) {
            return new JavaParserInterfaceDeclaration(this.wrappedNode, typeSolver);
        } else {
            return new JavaParserClassDeclaration(this.wrappedNode, typeSolver);
        }
    }

    public List<MethodDeclaration> methodsByName(String name) {
        List<MethodDeclaration> candidateMethods = new ArrayList<>();
        for (BodyDeclaration member : this.wrappedNode.getMembers()) {
            if (member instanceof com.github.javaparser.ast.body.MethodDeclaration) {
                com.github.javaparser.ast.body.MethodDeclaration method = (com.github.javaparser.ast.body.MethodDeclaration) member;
                if (method.getName().equals(name)) {
                    candidateMethods.add(new JavaParserMethodDeclaration(method, typeSolver));
                }
            }
        }
        return candidateMethods;
    }

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<Type> parameterTypes, TypeSolver typeSolver) {
        List<MethodDeclaration> candidateMethods = methodsByName(name);

        if (this.wrappedNode.getExtends() != null && !this.wrappedNode.getExtends().isEmpty()) {
            if (this.wrappedNode.getExtends().size() > 1) {
                throw new UnsupportedOperationException();
            }
            String superclassName = this.wrappedNode.getExtends().get(0).getName();
            SymbolReference<TypeDeclaration> superclass = solveType(superclassName, typeSolver);
            if (!superclass.isSolved()) {
                throw new UnsolvedSymbolException(this, superclassName);
            }
            SymbolReference<MethodDeclaration> res = MethodResolutionLogic.solveMethodInType(superclass.getCorrespondingDeclaration(), name, parameterTypes, typeSolver);
            if (res.isSolved()) {
                candidateMethods.add(res.getCorrespondingDeclaration());
            }
        } else {
            String superclassName = "java.lang.Object";
            SymbolReference<TypeDeclaration> superclass = solveType(superclassName, typeSolver);
            if (!superclass.isSolved()) {
                throw new UnsolvedSymbolException(this, superclassName);
            }
            SymbolReference<MethodDeclaration> res = MethodResolutionLogic.solveMethodInType(superclass.getCorrespondingDeclaration(), name, parameterTypes, typeSolver);
            if (res.isSolved()) {
                candidateMethods.add(res.getCorrespondingDeclaration());
            }
        }

        // Consider only default methods from interfaces
        for (ClassOrInterfaceType implemented : this.wrappedNode.getImplements()) {
            String interfaceClassName = implemented.getName();
            SymbolReference<TypeDeclaration> superclass = solveType(interfaceClassName, typeSolver);
            if (!superclass.isSolved()) {
                throw new UnsolvedSymbolException(this, interfaceClassName);
            }
            SymbolReference<MethodDeclaration> res = MethodResolutionLogic.solveMethodInType(superclass.getCorrespondingDeclaration(), name, parameterTypes, typeSolver);
            if (res.isSolved() && res.getCorrespondingDeclaration().isDefaultMethod()) {
                candidateMethods.add(res.getCorrespondingDeclaration());
            }
        }

        // We want to avoid infinite recursion when a class is using its own method
        // see issue #75
        if (candidateMethods.isEmpty()) {
            SymbolReference<MethodDeclaration> parentSolution = getParent().solveMethod(name, parameterTypes, typeSolver);
            if (parentSolution.isSolved()) {
                candidateMethods.add(parentSolution.getCorrespondingDeclaration());
            }
        }

        return MethodResolutionLogic.findMostApplicable(candidateMethods, name, parameterTypes, typeSolver);
    }
}
