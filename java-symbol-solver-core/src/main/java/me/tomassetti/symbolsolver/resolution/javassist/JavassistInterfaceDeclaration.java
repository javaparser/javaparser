package me.tomassetti.symbolsolver.resolution.javassist;

import javassist.CtClass;
import javassist.CtMethod;
import javassist.NotFoundException;
import javassist.bytecode.BadBytecode;
import javassist.bytecode.SignatureAttribute;
import me.tomassetti.symbolsolver.logic.AbstractTypeDeclaration;
import me.tomassetti.symbolsolver.logic.MethodResolutionLogic;
import me.tomassetti.symbolsolver.model.declarations.*;
import me.tomassetti.symbolsolver.model.invokations.MethodUsage;
import me.tomassetti.symbolsolver.model.resolution.Context;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.resolution.TypeParameter;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.typesystem.ReferenceTypeUsage;
import me.tomassetti.symbolsolver.model.typesystem.ReferenceTypeUsageImpl;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import me.tomassetti.symbolsolver.resolution.SymbolSolver;
import me.tomassetti.symbolsolver.resolution.javassist.contexts.JavassistMethodContext;

import java.sql.Ref;
import java.util.*;
import java.util.stream.Collectors;

public class JavassistInterfaceDeclaration extends AbstractTypeDeclaration implements InterfaceDeclaration {

    private CtClass ctClass;
    private TypeSolver typeSolver;

    public JavassistInterfaceDeclaration(CtClass ctClass, TypeSolver typeSolver) {
        this.ctClass = ctClass;
        this.typeSolver = typeSolver;
        if (!ctClass.isInterface()) {
            throw new IllegalArgumentException();
        }
    }

    @Override
    public List<InterfaceDeclaration> getInterfacesExtended() {
        throw new UnsupportedOperationException();
    }

    @Override
    public String getQualifiedName() {
        return ctClass.getName();
    }

    @Override
    public Context getContext() {
        throw new UnsupportedOperationException();
    }

    private List<TypeUsage> parseTypeParameters(String signature, TypeSolver typeSolver, Context context, Context invokationContext) {
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
            List<TypeUsage> typeUsages = new ArrayList<>();
            typeUsages.add(new SymbolSolver(typeSolver).solveTypeUsage(signature, invokationContext));
            return typeUsages;
        } else {
            return Collections.emptyList();
        }
    }

    @Override
    public Optional<MethodUsage> solveMethodAsUsage(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver,
                                                    Context invokationContext, List<TypeUsage> typeParameterValues) {

        // TODO avoid bridge and synthetic methods
        for (CtMethod method : ctClass.getDeclaredMethods()) {
            if (method.getName().equals(name)) {
                // TODO check parameters
                MethodUsage methodUsage = new MethodUsage(new JavassistMethodDeclaration(method, typeSolver), typeSolver);
                try {
                    if (method.getGenericSignature() != null) {
                        SignatureAttribute.MethodSignature classSignature = SignatureAttribute.toMethodSignature(method.getGenericSignature());
                        List<TypeUsage> parametersOfReturnType = parseTypeParameters(classSignature.getReturnType().toString(), typeSolver, new JavassistMethodContext(method), invokationContext);
                        TypeUsage newReturnType = methodUsage.returnType();
                        for (int i = 0; i < parametersOfReturnType.size(); i++) {
                            newReturnType = newReturnType.asReferenceTypeUsage().replaceParam(i, parametersOfReturnType.get(i));
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

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes) {
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
    public boolean isAssignableBy(TypeUsage typeUsage) {
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
    public boolean isAssignableBy(TypeDeclaration other) {
        throw new UnsupportedOperationException();
    }

    @Override
    public SymbolReference<? extends ValueDeclaration> solveSymbol(String substring, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }

    @Override
    public SymbolReference<TypeDeclaration> solveType(String substring, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<ReferenceTypeUsage> getAllAncestors() {
        List<ReferenceTypeUsage> ancestors = new ArrayList<>();
        try {
            for (CtClass interfaze : ctClass.getInterfaces()) {
                ReferenceTypeUsage superInterfaze = JavassistFactory.typeUsageFor(interfaze, typeSolver()).asReferenceTypeUsage();
                ancestors.add(superInterfaze);
                ancestors.addAll(superInterfaze.getAllAncestors());
            }
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }
        ancestors = ancestors.stream().filter(a -> a.getQualifiedName() != Object.class.getCanonicalName())
                .collect(Collectors.toList());
        ancestors.add(new ReferenceTypeUsageImpl(typeSolver.solveType(Object.class.getCanonicalName()), typeSolver));
        return ancestors;
    }

    @Override
    public Set<MethodDeclaration> getDeclaredMethods() {
        return Arrays.stream(ctClass.getDeclaredMethods())
                .map(m -> new JavassistMethodDeclaration(m, typeSolver()))
                .collect(Collectors.toSet());
    }

    @Override
    public String getName() {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<TypeParameter> getTypeParameters() {
        if (null == ctClass.getGenericSignature()) {
            return Collections.emptyList();
        } else {
            try {
                SignatureAttribute.ClassSignature classSignature = SignatureAttribute.toClassSignature(ctClass.getGenericSignature());
                return Arrays.<SignatureAttribute.TypeParameter>stream(classSignature.getParameters()).map((tp) -> new JavassistTypeParameter(tp, true, typeSolver)).collect(Collectors.toList());
            } catch (BadBytecode badBytecode) {
                throw new RuntimeException(badBytecode);
            }
        }
    }


}
