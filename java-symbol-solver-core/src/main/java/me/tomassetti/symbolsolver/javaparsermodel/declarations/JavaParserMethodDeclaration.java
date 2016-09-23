package me.tomassetti.symbolsolver.javaparsermodel.declarations;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFacade;
import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFactory;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ParameterDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.invokations.MethodUsage;
import me.tomassetti.symbolsolver.model.resolution.Context;
import me.tomassetti.symbolsolver.model.resolution.TypeParameter;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.typesystem.ReferenceTypeUsage;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import me.tomassetti.symbolsolver.model.typesystem.WildcardUsage;

import java.util.*;
import java.util.stream.Collectors;

public class JavaParserMethodDeclaration implements MethodDeclaration {

    private com.github.javaparser.ast.body.MethodDeclaration wrappedNode;
    private TypeSolver typeSolver;

    public JavaParserMethodDeclaration(com.github.javaparser.ast.body.MethodDeclaration wrappedNode, TypeSolver typeSolver) {
        this.wrappedNode = wrappedNode;
        this.typeSolver = typeSolver;
    }

    @Override
    public String toString() {
        return "JavaParserMethodDeclaration{" +
                "wrappedNode=" + wrappedNode +
                ", typeSolver=" + typeSolver +
                '}';
    }

    @Override
    public TypeDeclaration declaringType() {
        if (wrappedNode.getParentNode() instanceof ClassOrInterfaceDeclaration) {
            return new JavaParserClassDeclaration((ClassOrInterfaceDeclaration) wrappedNode.getParentNode(), typeSolver);
        } else {
            throw new UnsupportedOperationException();
        }
    }

    @Override
    public TypeUsage getReturnType() {
        return JavaParserFacade.get(typeSolver).convert(wrappedNode.getType(), getContext());
    }

    @Override
    public int getNoParams() {
        if (wrappedNode.getParameters() == null) {
            return 0;
        }
        return wrappedNode.getParameters().size();
    }

    @Override
    public ParameterDeclaration getParam(int i) {
        return new JavaParserParameterDeclaration(wrappedNode.getParameters().get(i), typeSolver);
    }

    public MethodUsage getUsage(Node node) {
        throw new UnsupportedOperationException();
    }

    @Override
    public MethodUsage resolveTypeVariables(Context context, List<TypeUsage> parameterTypes) {
        TypeUsage returnType = replaceTypeParams(new JavaParserMethodDeclaration(wrappedNode, typeSolver).getReturnType(), typeSolver, context);
        List<TypeUsage> params = new ArrayList<>();
        for (int i = 0; i < wrappedNode.getParameters().size(); i++) {
            TypeUsage replaced = replaceTypeParams(new JavaParserMethodDeclaration(wrappedNode, typeSolver).getParam(i).getType(), typeSolver, context);
            params.add(replaced);
        }

        // We now look at the type parameter for the method which we can derive from the parameter types
        // and then we replace them in the return type
        Map<String, TypeUsage> determinedTypeParameters = new HashMap<>();
        for (int i = 0; i < getNoParams(); i++) {
            TypeUsage formalParamType = getParam(i).getType();
            TypeUsage actualParamType = parameterTypes.get(i);
            determineTypeParameters(determinedTypeParameters, formalParamType, actualParamType, typeSolver);
        }

        for (String determinedParam : determinedTypeParameters.keySet()) {
            returnType = returnType.replaceParam(determinedParam, determinedTypeParameters.get(determinedParam));
        }

        return new MethodUsage(new JavaParserMethodDeclaration(wrappedNode, typeSolver), params, returnType);
    }

    private void determineTypeParameters(Map<String, TypeUsage> determinedTypeParameters, TypeUsage formalParamType, TypeUsage actualParamType, TypeSolver typeSolver) {
        if (actualParamType.isNull()) {
            return;
        }
        if (actualParamType.isTypeVariable()) {
            return;
        }
        if (formalParamType.isTypeVariable()) {
            determinedTypeParameters.put(formalParamType.describe(), actualParamType);
            return;
        }
        if (formalParamType instanceof WildcardUsage) {
            return;
        }
        if (formalParamType.isReferenceType() && actualParamType.isReferenceType()
                && !formalParamType.asReferenceTypeUsage().getQualifiedName().equals(actualParamType.asReferenceTypeUsage().getQualifiedName())) {
            List<ReferenceTypeUsage> ancestors = actualParamType.asReferenceTypeUsage().getAllAncestors();
            final String formalParamTypeQName = formalParamType.asReferenceTypeUsage().getQualifiedName();
            List<TypeUsage> correspondingFormalType = ancestors.stream().filter((a) -> a.getQualifiedName().equals(formalParamTypeQName)).collect(Collectors.toList());
            if (correspondingFormalType.isEmpty()) {
                throw new IllegalArgumentException();
            }
            actualParamType = correspondingFormalType.get(0);
        }
        if (formalParamType.isReferenceType() && actualParamType.isReferenceType()) {
            List<TypeUsage> formalTypeParams = formalParamType.asReferenceTypeUsage().parameters();
            List<TypeUsage> actualTypeParams = actualParamType.asReferenceTypeUsage().parameters();
            if (formalTypeParams.size() != actualTypeParams.size()) {
                throw new UnsupportedOperationException();
            }
            for (int i = 0; i < formalTypeParams.size(); i++) {
                determineTypeParameters(determinedTypeParameters, formalTypeParams.get(i), actualTypeParams.get(i), typeSolver);
            }
        }
    }

    private Context getContext() {
        return JavaParserFactory.getContext(wrappedNode, typeSolver);
    }

    @Override
    public boolean isAbstract() {
        return (wrappedNode.getBody() == null);
    }

    @Override
    public boolean isPrivate() {
        return wrappedNode.getModifiers().contains(com.github.javaparser.ast.Modifier.PRIVATE);
    }

    private Optional<TypeUsage> typeParamByName(String name, TypeSolver typeSolver, Context context) {
        int i = 0;
        if (wrappedNode.getTypeParameters() != null) {
            for (com.github.javaparser.ast.TypeParameter tp : wrappedNode.getTypeParameters()) {
                if (tp.getName().equals(name)) {
                    TypeUsage typeUsage = JavaParserFacade.get(typeSolver).convertToUsage(this.wrappedNode.getParameters().get(i).getType(), context);
                    return Optional.of(typeUsage);
                }
                i++;
            }
        }
        return Optional.empty();
    }

    private TypeUsage replaceTypeParams(TypeUsage typeUsage, TypeSolver typeSolver, Context context) {
        if (typeUsage.isTypeVariable()) {
            TypeParameter typeParameter = typeUsage.asTypeParameter();
            if (typeParameter.declaredOnClass()) {
                Optional<TypeUsage> typeParam = typeParamByName(typeParameter.getName(), typeSolver, context);
                if (typeParam.isPresent()) {
                    typeUsage = typeParam.get();
                }
            }
        }

        if (typeUsage.isReferenceType()) {
            for (int i = 0; i < typeUsage.asReferenceTypeUsage().parameters().size(); i++) {
                TypeUsage replaced = replaceTypeParams(typeUsage.asReferenceTypeUsage().parameters().get(i), typeSolver, context);
                // Identity comparison on purpose
                if (replaced != typeUsage.asReferenceTypeUsage().parameters().get(i)) {
                    typeUsage = typeUsage.asReferenceTypeUsage().replaceParam(i, replaced);
                }
            }
        }

        return typeUsage;
    }

    @Override
    public String getName() {
        return wrappedNode.getName();
    }

    @Override
    public boolean isField() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isParameter() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isVariable() {
        return false;
    }

    @Override
    public boolean isType() {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<TypeParameter> getTypeParameters() {
        if (this.wrappedNode.getTypeParameters() == null) {
            return Collections.emptyList();
        }
        return this.wrappedNode.getTypeParameters().stream().map((astTp) -> new JavaParserTypeParameter(astTp, typeSolver)).collect(Collectors.toList());
    }

    @Override
    public boolean isPackageProtected() {
        throw new UnsupportedOperationException();
    }

	/**
	 * Returns the JavaParser node associated with this JavaParserMethodDeclaration.
	 *
	 * @return A visitable JavaParser node wrapped by this object.
	 */
	public com.github.javaparser.ast.body.MethodDeclaration getWrappedNode()
	{
		return wrappedNode;
	}
}
