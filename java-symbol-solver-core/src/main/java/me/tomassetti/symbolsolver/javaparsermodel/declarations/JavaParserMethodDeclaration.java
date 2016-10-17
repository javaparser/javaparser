package me.tomassetti.symbolsolver.javaparsermodel.declarations;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;

import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFacade;
import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFactory;
import me.tomassetti.symbolsolver.model.declarations.AccessLevel;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ParameterDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.usages.MethodUsage;
import me.tomassetti.symbolsolver.core.resolution.Context;
import me.tomassetti.symbolsolver.model.declarations.TypeParameterDeclaration;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.usages.typesystem.ReferenceType;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;
import me.tomassetti.symbolsolver.model.usages.typesystem.Wildcard;

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
            ClassOrInterfaceDeclaration parent = (ClassOrInterfaceDeclaration) wrappedNode.getParentNode();
            if (parent.isInterface()) {
                return new JavaParserInterfaceDeclaration(parent, typeSolver);
            } else {
                return new JavaParserClassDeclaration(parent, typeSolver);
            }
        } else if (wrappedNode.getParentNode() instanceof EnumDeclaration) {
            return new JavaParserEnumDeclaration((EnumDeclaration) wrappedNode.getParentNode(), typeSolver);
        } else {
            throw new UnsupportedOperationException();
        }
    }

    @Override
    public Type getReturnType() {
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
        if (i < 0 || i >= getNoParams()) {
            throw new IllegalArgumentException(String.format("No param with index %d. Number of params: %d", i, getNoParams()));
        }
        return new JavaParserParameterDeclaration(wrappedNode.getParameters().get(i), typeSolver);
    }

    public MethodUsage getUsage(Node node) {
        throw new UnsupportedOperationException();
    }

    public MethodUsage resolveTypeVariables(Context context, List<Type> parameterTypes) {
        Type returnType = replaceTypeParams(new JavaParserMethodDeclaration(wrappedNode, typeSolver).getReturnType(), typeSolver, context);
        List<Type> params = new ArrayList<>();
        for (int i = 0; i < wrappedNode.getParameters().size(); i++) {
            Type replaced = replaceTypeParams(new JavaParserMethodDeclaration(wrappedNode, typeSolver).getParam(i).getType(), typeSolver, context);
            params.add(replaced);
        }

        // We now look at the type parameter for the method which we can derive from the parameter types
        // and then we replace them in the return type
        Map<String, Type> determinedTypeParameters = new HashMap<>();
        for (int i = 0; i < getNoParams(); i++) {
            Type formalParamType = getParam(i).getType();
            Type actualParamType = parameterTypes.get(i);
            determineTypeParameters(determinedTypeParameters, formalParamType, actualParamType, typeSolver);
        }

        for (String determinedParam : determinedTypeParameters.keySet()) {
            returnType = returnType.replaceParam(determinedParam, determinedTypeParameters.get(determinedParam));
        }

        return new MethodUsage(new JavaParserMethodDeclaration(wrappedNode, typeSolver), params, returnType);
    }

    private void determineTypeParameters(Map<String, Type> determinedTypeParameters, Type formalParamType, Type actualParamType, TypeSolver typeSolver) {
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
        if (formalParamType instanceof Wildcard) {
            return;
        }
        if (formalParamType.isArray() && actualParamType.isArray()) {
            determineTypeParameters(
                    determinedTypeParameters,
                    formalParamType.asArrayType().getComponentType(),
                    actualParamType.asArrayType().getComponentType(),
                    typeSolver);
            return;
        }
        if (formalParamType.isReferenceType() && actualParamType.isReferenceType()
                && !formalParamType.asReferenceType().getQualifiedName().equals(actualParamType.asReferenceType().getQualifiedName())) {
            List<ReferenceType> ancestors = actualParamType.asReferenceType().getAllAncestors();
            final String formalParamTypeQName = formalParamType.asReferenceType().getQualifiedName();
            List<Type> correspondingFormalType = ancestors.stream().filter((a) -> a.getQualifiedName().equals(formalParamTypeQName)).collect(Collectors.toList());
            if (correspondingFormalType.isEmpty()) {
                throw new IllegalArgumentException();
            }
            actualParamType = correspondingFormalType.get(0);
        }
        if (formalParamType.isReferenceType() && actualParamType.isReferenceType()) {
            if (formalParamType.asReferenceType().isRawType() || actualParamType.asReferenceType().isRawType()) {
                return;
            }
            List<Type> formalTypeParams = formalParamType.asReferenceType().typeParametersValues();
            List<Type> actualTypeParams = actualParamType.asReferenceType().typeParametersValues();
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

    private Optional<Type> typeParamByName(String name, TypeSolver typeSolver, Context context) {
        int i = 0;
        if (wrappedNode.getTypeParameters() != null) {
            for (com.github.javaparser.ast.TypeParameter tp : wrappedNode.getTypeParameters()) {
                if (tp.getName().equals(name)) {
                    Type type = JavaParserFacade.get(typeSolver).convertToUsage(this.wrappedNode.getParameters().get(i).getType(), context);
                    return Optional.of(type);
                }
                i++;
            }
        }
        return Optional.empty();
    }

    private Type replaceTypeParams(Type type, TypeSolver typeSolver, Context context) {
        if (type.isTypeVariable()) {
            TypeParameterDeclaration typeParameter = type.asTypeParameter();
            if (typeParameter.declaredOnClass()) {
                Optional<Type> typeParam = typeParamByName(typeParameter.getName(), typeSolver, context);
                if (typeParam.isPresent()) {
                    type = typeParam.get();
                }
            }
        }

        if (type.isReferenceType()) {
            for (int i = 0; i < type.asReferenceType().typeParametersValues().size(); i++) {
                Type replaced = replaceTypeParams(type.asReferenceType().typeParametersValues().get(i), typeSolver, context);
                // Identity comparison on purpose
                if (replaced != type.asReferenceType().typeParametersValues().get(i)) {
                    type = type.asReferenceType().replaceParam(i, replaced);
                }
            }
        }

        return type;
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
    public boolean isType() {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<TypeParameterDeclaration> getTypeParameters() {
        if (this.wrappedNode.getTypeParameters() == null) {
            return Collections.emptyList();
        }
        return this.wrappedNode.getTypeParameters().stream().map((astTp) -> new JavaParserTypeParameter(astTp, typeSolver)).collect(Collectors.toList());
    }

    @Override
    public boolean isDefaultMethod() {
        return wrappedNode.isDefault();
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

    @Override
    public AccessLevel accessLevel() {
        throw new UnsupportedOperationException();
    }
}
