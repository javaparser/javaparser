package me.tomassetti.symbolsolver.reflectionmodel;

import com.github.javaparser.ast.Node;
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

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.*;
import java.util.stream.Collectors;

public class ReflectionMethodDeclaration implements MethodDeclaration {

    // TODO
    // This class contains a huge portion of code just copied from JavaParserMethodDeclaration

    private Method method;
    private TypeSolver typeSolver;

    public ReflectionMethodDeclaration(Method method, TypeSolver typeSolver) {
        this.method = method;
        if (method.isSynthetic() || method.isBridge()) {
            throw new IllegalArgumentException();
        }
        this.typeSolver = typeSolver;
    }

    @Override
    public String getName() {
        return method.getName();
    }

    @Override
    public boolean isField() {
        return false;
    }

    @Override
    public boolean isParameter() {
        return false;
    }

    @Override
    public String toString() {
        return "ReflectionMethodDeclaration{" +
                "method=" + method +
                '}';
    }

    @Override
    public boolean isType() {
        return false;
    }

    @Override
    public TypeDeclaration declaringType() {
        if (method.getDeclaringClass().isInterface()) {
            return new ReflectionInterfaceDeclaration(method.getDeclaringClass(), typeSolver);
        } else {
            return new ReflectionClassDeclaration(method.getDeclaringClass(), typeSolver);
        }
    }

    @Override
    public Type getReturnType() {
        return ReflectionFactory.typeUsageFor(method.getGenericReturnType(), typeSolver);
    }

    @Override
    public int getNoParams() {
        return method.getParameterTypes().length;
    }

    @Override
    public ParameterDeclaration getParam(int i) {
        boolean variadic = false;
        if (method.isVarArgs()) {
            variadic = i == (method.getParameterCount() - 1);
        }
        return new ReflectionParameterDeclaration(method.getParameterTypes()[i], method.getGenericParameterTypes()[i], typeSolver, variadic);
    }

    public MethodUsage getUsage(Node node) {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<TypeParameterDeclaration> getTypeParameters() {
        return Arrays.stream(method.getTypeParameters()).map((refTp) -> new ReflectionTypeParameter(refTp, false)).collect(Collectors.toList());
    }

    //@Override
    public MethodUsage resolveTypeVariables(Context context, List<Type> parameterTypes) {
        //return new MethodUsage(new ReflectionMethodDeclaration(method, typeSolver), typeSolver);
        Type returnType = replaceTypeParams(new ReflectionMethodDeclaration(method, typeSolver).getReturnType(), typeSolver, context);
        List<Type> params = new ArrayList<>();
        for (int i = 0; i < method.getParameterCount(); i++) {
            Type replaced = replaceTypeParams(new ReflectionMethodDeclaration(method, typeSolver).getParam(i).getType(), typeSolver, context);
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

        return new MethodUsage(new ReflectionMethodDeclaration(method, typeSolver), params, returnType);
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

    private Optional<Type> typeParamByName(String name, TypeSolver typeSolver, Context context) {
        int i = 0;
        if (this.getTypeParameters() != null) {
            for (TypeParameterDeclaration tp : this.getTypeParameters()) {
                if (tp.getName().equals(name)) {
                    Type type = this.getParam(i).getType();
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
    public boolean isAbstract() {
        return Modifier.isAbstract(method.getModifiers());
    }

    @Override
    public boolean isDefaultMethod() {
        return method.isDefault();
    }

    @Override
    public AccessLevel accessLevel() {
        return ReflectionFactory.modifiersToAccessLevel(this.method.getModifiers());
    }

}
