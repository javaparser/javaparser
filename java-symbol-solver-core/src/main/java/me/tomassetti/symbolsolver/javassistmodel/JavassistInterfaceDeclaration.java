package me.tomassetti.symbolsolver.javassistmodel;

import javassist.CtClass;
import javassist.CtMethod;
import javassist.NotFoundException;
import javassist.bytecode.BadBytecode;
import javassist.bytecode.SignatureAttribute;
import me.tomassetti.symbolsolver.logic.AbstractTypeDeclaration;
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
import me.tomassetti.symbolsolver.resolution.SymbolSolver;
import me.tomassetti.symbolsolver.javassistmodel.contexts.JavassistMethodContext;

import java.util.*;
import java.util.stream.Collectors;

public class JavassistInterfaceDeclaration extends AbstractTypeDeclaration implements InterfaceDeclaration {

    private CtClass ctClass;

    @Override
    public String toString() {
        return "JavassistInterfaceDeclaration{" +
                "ctClass=" + ctClass.getName() +
                ", typeSolver=" + typeSolver +
                '}';
    }

    private TypeSolver typeSolver;

    public JavassistInterfaceDeclaration(CtClass ctClass, TypeSolver typeSolver) {
        this.ctClass = ctClass;
        this.typeSolver = typeSolver;
        if (!ctClass.isInterface()) {
            throw new IllegalArgumentException("Not an interface: " + ctClass.getName());
        }
    }

    @Override
    public List<ReferenceType> getInterfacesExtended() {
        try {
            return Arrays.stream(ctClass.getInterfaces()).map(i -> new JavassistInterfaceDeclaration(i, typeSolver))
                    .map(i -> new ReferenceTypeImpl(i, typeSolver)).collect(Collectors.toList());
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public String getQualifiedName() {
        return ctClass.getName();
    }

    public Context getContext() {
        throw new UnsupportedOperationException();
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

    @Deprecated
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
                Optional<MethodUsage> ref = new JavassistInterfaceDeclaration(interfaze, typeSolver).solveMethodAsUsage(name, parameterTypes, typeSolver, invokationContext, null);
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

    @Override
    protected TypeSolver typeSolver() {
        return typeSolver;
    }

    @Override
    public boolean isAssignableBy(Type type) {
        throw new UnsupportedOperationException();
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
    public boolean isAssignableBy(TypeDeclaration other) {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<ReferenceType> getAncestors() {
        List<ReferenceType> ancestors = new ArrayList<>();
        try {
            for (CtClass interfaze : ctClass.getInterfaces()) {
                ReferenceType superInterfaze = JavassistFactory.typeUsageFor(interfaze, typeSolver()).asReferenceType();
                ancestors.add(superInterfaze);
            }
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }
        ancestors = ancestors.stream().filter(a -> a.getQualifiedName() != Object.class.getCanonicalName())
                .collect(Collectors.toList());
        ancestors.add(new ReferenceTypeImpl(typeSolver.solveType(Object.class.getCanonicalName()), typeSolver));
        return ancestors;
    }

    @Override
    public Set<MethodDeclaration> getDeclaredMethods() {
        return Arrays.stream(ctClass.getDeclaredMethods())
                .map(m -> new JavassistMethodDeclaration(m, typeSolver()))
                .collect(Collectors.toSet());
    }

    @Override
    public boolean hasDirectlyAnnotation(String canonicalName) {
        try {
            for (Object annotationRaw : ctClass.getAnnotations()) {
                if (annotationRaw.getClass().getCanonicalName().equals(canonicalName)) {
                    return true;
                }
                if (Arrays.stream(annotationRaw.getClass().getInterfaces()).anyMatch(it -> it.getCanonicalName().equals(canonicalName))) {
                    return true;
                }
            }
        } catch (ClassNotFoundException e) {
            throw new RuntimeException(e);
        }
        return false;
    }

    @Override
    public String getName() {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<TypeParameterDeclaration> getTypeParameters() {
        if (null == ctClass.getGenericSignature()) {
            return Collections.emptyList();
        } else {
            try {
                SignatureAttribute.ClassSignature classSignature = SignatureAttribute.toClassSignature(ctClass.getGenericSignature());
                return Arrays.<SignatureAttribute.TypeParameter>stream(classSignature.getParameters()).map((tp) -> new JavassistTypeParameter(tp, true, ctClass.getName(), typeSolver)).collect(Collectors.toList());
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
    public InterfaceDeclaration asInterface() {
        return this;
    }
}
