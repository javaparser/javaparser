package me.tomassetti.symbolsolver.javassistmodel;

import com.github.javaparser.ast.Node;
import javassist.CtClass;
import javassist.CtField;
import javassist.CtMethod;
import javassist.NotFoundException;
import javassist.bytecode.BadBytecode;
import javassist.bytecode.SignatureAttribute;
import me.tomassetti.symbolsolver.logic.AbstractClassDeclaration;
import me.tomassetti.symbolsolver.resolution.MethodResolutionLogic;
import me.tomassetti.symbolsolver.model.declarations.*;
import me.tomassetti.symbolsolver.model.usages.MethodUsage;
import me.tomassetti.symbolsolver.core.resolution.Context;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.declarations.TypeParameterDeclaration;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.usages.typesystem.ReferenceType;
import me.tomassetti.symbolsolver.model.usages.typesystem.ReferenceTypeImpl;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;
import me.tomassetti.symbolsolver.resolution.*;
import me.tomassetti.symbolsolver.javaparsermodel.LambdaArgumentTypePlaceholder;
import me.tomassetti.symbolsolver.javassistmodel.contexts.JavassistMethodContext;

import java.util.*;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

public class JavassistClassDeclaration extends AbstractClassDeclaration {

    private CtClass ctClass;
    private TypeSolver typeSolver;

    @Override
    protected ReferenceType object() {
        return new ReferenceTypeImpl(typeSolver.solveType(Object.class.getCanonicalName()), typeSolver);
    }

    @Override
    public ClassDeclaration asClass() {
        return this;
    }

    @Override
    public boolean hasDirectlyAnnotation(String canonicalName) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Set<MethodDeclaration> getDeclaredMethods() {
        return Arrays.stream(ctClass.getDeclaredMethods())
                .map(m -> new JavassistMethodDeclaration(m, typeSolver()))
                .collect(Collectors.toSet());
    }

    public JavassistClassDeclaration(CtClass ctClass, TypeSolver typeSolver) {
        if (ctClass == null) {
            throw new IllegalArgumentException();
        }
        if (ctClass.isInterface() || ctClass.isAnnotation() || ctClass.isPrimitive() || ctClass.isEnum()) {
            throw new IllegalArgumentException("Trying to instantiate a JavassistClassDeclaration with something which is not a class: " + ctClass.toString());
        }
        this.ctClass = ctClass;
        this.typeSolver = typeSolver;
    }

    @Override
    protected TypeSolver typeSolver() {
        return typeSolver;
    }

    @Override
    public boolean isAssignableBy(TypeDeclaration other) {
        return isAssignableBy(new ReferenceTypeImpl(other, typeSolver));
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        JavassistClassDeclaration that = (JavassistClassDeclaration) o;

        if (!ctClass.equals(that.ctClass)) return false;

        return true;
    }

    @Override
    public int hashCode() {
        return ctClass.hashCode();
    }

    @Override
    public String getQualifiedName() {
        return ctClass.getName();
    }

    private List<Type> parseTypeParameters(String signature, TypeSolver typeSolver, Context context, Context invokationContext) {
        String originalSignature = signature;
        if (signature.contains("<")) {
            signature = signature.substring(signature.indexOf('<') + 1);
            if (!signature.endsWith(">")) {
                throw new IllegalArgumentException();
            }
            signature = signature.substring(0, signature.length() - 1);
            if (signature.contains(",")) {
                throw new UnsupportedOperationException();
            }
            if (signature.contains("<")) {
                throw new UnsupportedOperationException(originalSignature);
            }
            if (signature.contains(">")) {
                throw new UnsupportedOperationException();
            }
            List<Type> types = new ArrayList<>();
            types.add(new SymbolSolver(typeSolver).solveTypeUsage(signature, invokationContext));
            return types;
        } else {
            return Collections.emptyList();
        }
    }

    public Optional<MethodUsage> solveMethodAsUsage(String name, List<Type> parameterTypes, TypeSolver typeSolver,
                                                    Context invokationContext, List<Type> typeParameterValues) {

        // TODO avoid bridge and synthetic methods
        for (CtMethod method : ctClass.getDeclaredMethods()) {
            if (method.getName().equals(name)) {
                // TODO check typeParametersValues
                MethodUsage methodUsage = new MethodUsage(new JavassistMethodDeclaration(method, typeSolver));
                try {
                    if (method.getGenericSignature() != null) {
                        SignatureAttribute.MethodSignature classSignature = SignatureAttribute.toMethodSignature(method.getGenericSignature());
                        List<Type> parametersOfReturnType = parseTypeParameters(classSignature.getReturnType().toString(), typeSolver, new JavassistMethodContext(method), invokationContext);
                        Type newReturnType = methodUsage.returnType();
                        for (int i = 0; i < parametersOfReturnType.size(); i++) {
                            newReturnType = newReturnType.asReferenceType().replaceParam(i, parametersOfReturnType.get(i));
                        }
                        methodUsage = methodUsage.replaceReturnType(newReturnType);
                    }
                    return Optional.of(methodUsage);
                } catch (BadBytecode e) {
                    throw new RuntimeException(e);
                }
            }
        }

        try {
            CtClass superClass = ctClass.getSuperclass();
            if (superClass != null) {
                Optional<MethodUsage> ref = new JavassistClassDeclaration(superClass, typeSolver).solveMethodAsUsage(name, parameterTypes, typeSolver, invokationContext, null);
                if (ref.isPresent()) {
                    return ref;
                }
            }
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }

        try {
            for (CtClass interfaze : ctClass.getInterfaces()) {
                Optional<MethodUsage> ref = new JavassistClassDeclaration(interfaze, typeSolver).solveMethodAsUsage(name, parameterTypes, typeSolver, invokationContext, null);
                if (ref.isPresent()) {
                    return ref;
                }
            }
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }

        return Optional.empty();
    }

    @Deprecated
    public SymbolReference<? extends ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        for (CtField field : ctClass.getDeclaredFields()) {
            if (field.getName().equals(name)) {
                return SymbolReference.solved(new JavassistFieldDeclaration(field, typeSolver));
            }
        }

        try {
            CtClass superClass = ctClass.getSuperclass();
            if (superClass != null) {
                SymbolReference<? extends ValueDeclaration> ref = new JavassistClassDeclaration(superClass, typeSolver).solveSymbol(name, typeSolver);
                if (ref.isSolved()) {
                    return ref;
                }
            }
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }

        try {
            for (CtClass interfaze : ctClass.getInterfaces()) {
                SymbolReference<? extends ValueDeclaration> ref = new JavassistClassDeclaration(interfaze, typeSolver).solveSymbol(name, typeSolver);
                if (ref.isSolved()) {
                    return ref;
                }
            }
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }

        return SymbolReference.unsolved(ValueDeclaration.class);
    }

    @Override
    public List<ReferenceType> getAncestors() {
        List<ReferenceType> ancestors = new LinkedList<>();
        if (getSuperClass() != null) {
            ancestors.add(getSuperClass());
        }
        ancestors.addAll(getInterfaces());
        return ancestors;
    }

    public Context getContext() {
        throw new UnsupportedOperationException();
    }

    @Deprecated
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<Type> parameterTypes) {
        List<MethodDeclaration> candidates = new ArrayList<>();
        for (CtMethod method : ctClass.getDeclaredMethods()) {
            // TODO avoid bridge and synthetic methods
            if (method.getName().equals(name)) {
                candidates.add(new JavassistMethodDeclaration(method, typeSolver));
            }
        }

        try {
            CtClass superClass = ctClass.getSuperclass();
            if (superClass != null) {
                SymbolReference<MethodDeclaration> ref = new JavassistClassDeclaration(superClass, typeSolver).solveMethod(name, parameterTypes);
                if (ref.isSolved()) {
                    candidates.add(ref.getCorrespondingDeclaration());
                }
            }
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }

        try {
            for (CtClass interfaze : ctClass.getInterfaces()) {
                SymbolReference<MethodDeclaration> ref = new JavassistInterfaceDeclaration(interfaze, typeSolver).solveMethod(name, parameterTypes);
                if (ref.isSolved()) {
                    candidates.add(ref.getCorrespondingDeclaration());
                }
            }
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }

        return MethodResolutionLogic.findMostApplicable(candidates, name, parameterTypes, typeSolver);
    }

    public Type getUsage(Node node) {
        return new ReferenceTypeImpl(this, typeSolver);
    }

    @Override
    public boolean isAssignableBy(Type type) {
        if (type.isNull()) {
            return true;
        }

        if (type instanceof LambdaArgumentTypePlaceholder) {
            if (ctClass.getName().equals(Predicate.class.getCanonicalName()) || ctClass.getName().equals(Function.class.getCanonicalName())) {
                return true;
            } else {
                return false;
            }
        }

        // TODO look into generics
        if (type.describe().equals(this.getQualifiedName())) {
            return true;
        }
        try {
            if (this.ctClass.getSuperclass() != null
                    && new JavassistClassDeclaration(this.ctClass.getSuperclass(), typeSolver).isAssignableBy(type)) {
                    return true;
            }
            for (CtClass interfaze : ctClass.getInterfaces()) {
                if (new JavassistClassDeclaration(interfaze, typeSolver).isAssignableBy(type)) {
                    return true;
                }
            }
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }
        return false;
    }

    @Override
    public boolean isTypeVariable() {
        return false;
    }

    @Override
    public FieldDeclaration getField(String name) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean hasField(String name) {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<FieldDeclaration> getAllFields() {
        throw new UnsupportedOperationException();
    }

    @Override
    public String getName() {
        return ctClass.getSimpleName();
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
    public boolean isType() {
        return true;
    }

    @Override
    public boolean isClass() {
        return !ctClass.isInterface();
    }

    @Override
    public ReferenceTypeImpl getSuperClass() {
        try {
            if (ctClass.getSuperclass() == null) {
                return new ReferenceTypeImpl(typeSolver.solveType(Object.class.getCanonicalName()), typeSolver());
            }
            return new ReferenceTypeImpl(new JavassistClassDeclaration(ctClass.getSuperclass(), typeSolver).asClass(), typeSolver);
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public List<ReferenceType> getInterfaces() {
        try {
            return Arrays.stream(ctClass.getInterfaces())
                    .map(i -> new JavassistInterfaceDeclaration(i, typeSolver()))
                    .map(i -> new ReferenceTypeImpl(i, typeSolver()))
                    .collect(Collectors.toList());
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public boolean isInterface() {
        return ctClass.isInterface();
    }

    @Override
    public String toString() {
        return "JavassistClassDeclaration {" + ctClass.getName() + '}';
    }

    @Override
    public List<TypeParameterDeclaration> getTypeParameters() {
        if (null == ctClass.getGenericSignature()) {
            return Collections.emptyList();
        } else {
            try {
                SignatureAttribute.ClassSignature classSignature = SignatureAttribute.toClassSignature(ctClass.getGenericSignature());
                String qualifier = ctClass.getName();
                return Arrays.<SignatureAttribute.TypeParameter>stream(classSignature.getParameters()).map((tp) -> new JavassistTypeParameter(tp, true, qualifier, typeSolver)).collect(Collectors.toList());
            } catch (BadBytecode badBytecode) {
                throw new RuntimeException(badBytecode);
            }
        }
    }

    @Override
    public AccessLevel accessLevel() {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<ConstructorDeclaration> getConstructors() {
        throw new UnsupportedOperationException();
    }
}
