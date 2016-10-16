package me.tomassetti.symbolsolver.resolution;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.ReferenceType;
import me.tomassetti.symbolsolver.core.resolution.Context;
import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFactory;
import me.tomassetti.symbolsolver.javaparsermodel.UnsolvedSymbolException;
import me.tomassetti.symbolsolver.javaparsermodel.declarations.JavaParserClassDeclaration;
import me.tomassetti.symbolsolver.javaparsermodel.declarations.JavaParserEnumDeclaration;
import me.tomassetti.symbolsolver.javaparsermodel.declarations.JavaParserInterfaceDeclaration;
import me.tomassetti.symbolsolver.javassistmodel.JavassistClassDeclaration;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.resolution.Value;
import me.tomassetti.symbolsolver.model.usages.MethodUsage;
import me.tomassetti.symbolsolver.model.usages.typesystem.ReferenceTypeImpl;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;
import me.tomassetti.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import me.tomassetti.symbolsolver.reflectionmodel.ReflectionInterfaceDeclaration;

import java.util.List;
import java.util.Optional;

public class SymbolSolver {

    private TypeSolver typeSolver;

    public SymbolSolver(TypeSolver typeSolver) {
        if (typeSolver == null) throw new IllegalArgumentException();

        this.typeSolver = typeSolver;
    }

    public SymbolReference<? extends ValueDeclaration> solveSymbol(String name, Context context) {
        return context.solveSymbol(name, typeSolver);
    }

    public SymbolReference<? extends ValueDeclaration> solveSymbol(String name, Node node) {
        return solveSymbol(name, JavaParserFactory.getContext(node, typeSolver));
    }

    public Optional<Value> solveSymbolAsValue(String name, Context context) {
        return context.solveSymbolAsValue(name, typeSolver);
    }

    public Optional<Value> solveSymbolAsValue(String name, Node node) {
        Context context = JavaParserFactory.getContext(node, typeSolver);
        return solveSymbolAsValue(name, context);
    }

    public SymbolReference<? extends TypeDeclaration> solveType(String name, Context context) {
        return context.solveType(name, typeSolver);
    }

    public SymbolReference<? extends TypeDeclaration> solveType(String name, Node node) {
        return solveType(name, JavaParserFactory.getContext(node, typeSolver));
    }

    public MethodUsage solveMethod(String methodName, List<Type> params, Context context) {
        SymbolReference<MethodDeclaration> decl = context.solveMethod(methodName, params, typeSolver);
        if (!decl.isSolved()) {
            throw new UnsolvedSymbolException(context, methodName);
        }
        return new MethodUsage(decl.getCorrespondingDeclaration());
    }

    public MethodUsage solveMethod(String methodName, List<Type> params, Node node) {
        return solveMethod(methodName, params, JavaParserFactory.getContext(node, typeSolver));
    }

    ;

    public TypeDeclaration solveType(com.github.javaparser.ast.type.Type type) {
        if (type instanceof ReferenceType) {
            ReferenceType referenceType = (ReferenceType) type;
            // TODO consider array modifiers
            return solveType(referenceType.getType());
        } else if (type instanceof ClassOrInterfaceType) {

            // FIXME should call typesolver here!

            String name = ((ClassOrInterfaceType) type).getName();
            SymbolReference<TypeDeclaration> ref = JavaParserFactory.getContext(type, typeSolver).solveType(name, typeSolver);
            if (!ref.isSolved()) {
                throw new UnsolvedSymbolException(JavaParserFactory.getContext(type, typeSolver), name);
            }
            return ref.getCorrespondingDeclaration();
        } else {
            throw new UnsupportedOperationException(type.getClass().getCanonicalName());
        }
    }

    public Type solveTypeUsage(String name, Context context) {
        Optional<Type> genericType = context.solveGenericType(name, typeSolver);
        if (genericType.isPresent()) {
            return genericType.get();
        }
        TypeDeclaration typeDeclaration = typeSolver.solveType(name);
        ReferenceTypeImpl typeUsage = new ReferenceTypeImpl(typeDeclaration, typeSolver);
        return typeUsage;
    }

    /**
     * Solve any possible visible symbols including: fields, internal types, type variables, the type itself or its containers.
     *
     * It should contain its own private fields but not inherited private fields.
     */
    public SymbolReference<? extends ValueDeclaration> solveSymbolInType(TypeDeclaration typeDeclaration, String name) {
        if (typeDeclaration instanceof JavaParserClassDeclaration) {
            Context ctx = ((JavaParserClassDeclaration)typeDeclaration).getContext();
            return ctx.solveSymbol(name, typeSolver);
        }
        if (typeDeclaration instanceof JavaParserInterfaceDeclaration) {
            Context ctx = ((JavaParserInterfaceDeclaration)typeDeclaration).getContext();
            return ctx.solveSymbol(name, typeSolver);
        }
        if (typeDeclaration instanceof JavaParserEnumDeclaration) {
            Context ctx = ((JavaParserEnumDeclaration)typeDeclaration).getContext();
            return ctx.solveSymbol(name, typeSolver);
        }
        if (typeDeclaration instanceof ReflectionClassDeclaration) {
            return ((ReflectionClassDeclaration)typeDeclaration).solveSymbol(name, typeSolver);
        }
        if (typeDeclaration instanceof ReflectionInterfaceDeclaration) {
            return ((ReflectionInterfaceDeclaration)typeDeclaration).solveSymbol(name, typeSolver);
        }
        if (typeDeclaration instanceof JavassistClassDeclaration) {
            return ((JavassistClassDeclaration)typeDeclaration).solveSymbol(name, typeSolver);
        }
        return SymbolReference.unsolved(ValueDeclaration.class);
    }

    /**
     * Try to solve a symbol just in the declaration, it does not delegate to the container.
     */
    public SymbolReference<TypeDeclaration> solveTypeInType(TypeDeclaration typeDeclaration, String name) {
        if (typeDeclaration instanceof JavaParserClassDeclaration) {
            return ((JavaParserClassDeclaration)typeDeclaration).solveType(name, typeSolver);
        }
        if (typeDeclaration instanceof JavaParserInterfaceDeclaration) {
            return ((JavaParserInterfaceDeclaration)typeDeclaration).solveType(name, typeSolver);
        }
        return SymbolReference.unsolved(TypeDeclaration.class);
    }
}
