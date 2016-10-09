package me.tomassetti.symbolsolver.model.typesystem;

import me.tomassetti.symbolsolver.javaparsermodel.LambdaArgumentTypeUsagePlaceholder;
import me.tomassetti.symbolsolver.javaparsermodel.declarations.JavaParserTypeVariableDeclaration;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.invokations.MethodUsage;
import me.tomassetti.symbolsolver.model.resolution.TypeParameter;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

// TODO Remove references to typeSolver: it is needed to instantiate other instances of ReferenceTypeUsage
//      and to get the Object type declaration
public class ReferenceTypeUsageImpl extends ReferenceTypeUsage {

    @Override
    protected ReferenceTypeUsage create(TypeDeclaration typeDeclaration, List<TypeUsage> typeParametersCorrected, TypeSolver typeSolver) {
        return new ReferenceTypeUsageImpl(typeDeclaration, typeParametersCorrected, typeSolver);
    }

    @Override
    protected ReferenceTypeUsage create(TypeDeclaration typeDeclaration, TypeSolver typeSolver) {
        return new ReferenceTypeUsageImpl(typeDeclaration, typeSolver);
    }

    public ReferenceTypeUsageImpl(TypeDeclaration typeDeclaration, TypeSolver typeSolver) {
        super(typeDeclaration, typeSolver);
    }

    public ReferenceTypeUsageImpl(TypeDeclaration typeDeclaration, List<TypeUsage> typeParameters, TypeSolver typeSolver) {
        super(typeDeclaration, typeParameters, typeSolver);
    }

    @Override
    public TypeParameter asTypeParameter() {
        if (this.typeDeclaration instanceof JavaParserTypeVariableDeclaration) {
            JavaParserTypeVariableDeclaration javaParserTypeVariableDeclaration = (JavaParserTypeVariableDeclaration) this.typeDeclaration;
            return javaParserTypeVariableDeclaration.asTypeParameter();
        }
        throw new UnsupportedOperationException(this.typeDeclaration.getClass().getCanonicalName());
    }

    /**
     * This method checks if ThisType t = new OtherType() would compile.
     */
    @Override
    public boolean isAssignableBy(TypeUsage other) {
        if (other instanceof NullTypeUsage) {
            return !this.isPrimitive();
        }
        // consider boxing
        if (other.isPrimitive()) {
            if (this.getQualifiedName().equals(Object.class.getCanonicalName())) {
                return true;
            } else {
                return isCorrespondingBoxingType(other.describe());
            }
        }
        if (other instanceof LambdaArgumentTypeUsagePlaceholder) {
            return this.getTypeDeclaration().hasAnnotation(FunctionalInterface.class.getCanonicalName());
        } else if (other instanceof ReferenceTypeUsageImpl) {
            ReferenceTypeUsageImpl otherRef = (ReferenceTypeUsageImpl) other;
            if (compareConsideringTypeParameters(otherRef)) {
                return true;
            }
            for (ReferenceTypeUsage otherAncestor : otherRef.getAllAncestors()) {
                if (compareConsideringTypeParameters(otherAncestor)) {
                    return true;
                }
            }
            return false;
        } else if (other.isTypeVariable()) {
            // TODO look bounds...
            return true;
        } else if (other.isWildcard()) {
            if (this.getQualifiedName().equals(Object.class.getCanonicalName())) {
                return true;
            } else if (other.asWildcard().isExtends()) {
                return isAssignableBy(other.asWildcard().getBoundedType());
            } else {
                return false;
            }
        } else {
            return false;
        }
    }

    @Override
    public Set<MethodUsage> getDeclaredMethods() {
        // TODO replace variables
        Set<MethodUsage> methods = new HashSet<>();
        for (MethodDeclaration methodDeclaration : getTypeDeclaration().getDeclaredMethods()) {
            MethodUsage methodUsage = new MethodUsage(methodDeclaration, typeSolver);
            methods.add(methodUsage);
        }
        return methods;
    }


}
