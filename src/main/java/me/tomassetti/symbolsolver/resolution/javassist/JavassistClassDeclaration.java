package me.tomassetti.symbolsolver.resolution.javassist;

import com.github.javaparser.ast.Node;
import javassist.CtClass;
import javassist.CtField;
import javassist.CtMethod;
import javassist.NotFoundException;
import javassist.bytecode.BadBytecode;
import javassist.bytecode.SignatureAttribute;
import me.tomassetti.symbolsolver.logic.AbstractClassDeclaration;
import me.tomassetti.symbolsolver.logic.MethodResolutionLogic;
import me.tomassetti.symbolsolver.resolution.*;
import me.tomassetti.symbolsolver.model.declarations.*;
import me.tomassetti.symbolsolver.resolution.javassist.contexts.JavassistMethodContext;
import me.tomassetti.symbolsolver.resolution.javaparser.LambdaArgumentTypeUsagePlaceholder;
import me.tomassetti.symbolsolver.model.invokations.MethodUsage;
import me.tomassetti.symbolsolver.model.typesystem.ReferenceTypeUsage;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;


import java.util.*;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

public class JavassistClassDeclaration extends AbstractClassDeclaration {

    private CtClass ctClass;
    private TypeSolver typeSolver;

    @Override
    protected TypeSolver typeSolver() {
        return typeSolver;
    }

    @Override
    public boolean isAssignableBy(TypeDeclaration other) {
        return isAssignableBy(new ReferenceTypeUsage(other, typeSolver));
    }

    public JavassistClassDeclaration(CtClass ctClass, TypeSolver typeSolver) {
        if (ctClass == null) {
            throw new IllegalArgumentException();
        }
        this.ctClass = ctClass;
        this.typeSolver = typeSolver;
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

    private List<TypeUsage> parseTypeParameters(String signature, TypeSolver typeSolver, Context context, Context invokationContext) {
        String originalSignature = signature;
        if (signature.contains("<")) {
            signature = signature.substring(signature.indexOf('<') + 1);
            if (!signature.endsWith(">")) {
                throw new IllegalArgumentException();
            }
            signature = signature.substring(0, signature.length() - 1);
            if (signature.contains(",")){
                throw new UnsupportedOperationException();
            }
            if (signature.contains("<")){
                throw new UnsupportedOperationException(originalSignature);
            }
            if (signature.contains(">")){
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
            if (method.getName().equals(name)){
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
                } catch (BadBytecode e){
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

    @Override
    public SymbolReference<? extends ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        for (CtField field : ctClass.getDeclaredFields()) {
            if (field.getName().equals(name)){
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
    public SymbolReference<TypeDeclaration> solveType(String substring, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<ReferenceTypeUsage> getAllAncestors() {
        List<ReferenceTypeUsage> ancestors = new LinkedList<>();
        if (getSuperClass() != null) {
            ancestors.add(getSuperClass());
            ancestors.addAll(getSuperClass().getAllAncestors());
        }
        ancestors.addAll(getAllInterfaces().stream().map((i)->new ReferenceTypeUsage(i, typeSolver)).collect(Collectors.<ReferenceTypeUsage>toList()));
        return ancestors;
    }
    @Override
    public Context getContext() {
        throw new UnsupportedOperationException();
    }

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes) {
        List<MethodDeclaration> candidates = new ArrayList<>();
        for (CtMethod method : ctClass.getDeclaredMethods()) {
            // TODO avoid bridge and synthetic methods
            if (method.getName().equals(name)){
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
                SymbolReference<MethodDeclaration> ref = new JavassistClassDeclaration(interfaze, typeSolver).solveMethod(name, parameterTypes);
                if (ref.isSolved()) {
                    candidates.add(ref.getCorrespondingDeclaration());
                }
            }
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }

        return MethodResolutionLogic.findMostApplicable(candidates, name, parameterTypes, typeSolver);
    }

    public TypeUsage getUsage(Node node) {
        return new ReferenceTypeUsage(this, typeSolver);
    }

    @Override
    public boolean isAssignableBy(TypeUsage typeUsage) {
        if (typeUsage.isNull()) {
            return true;
        }

        if (typeUsage instanceof LambdaArgumentTypeUsagePlaceholder){
            if (ctClass.getName().equals(Predicate.class.getCanonicalName()) || ctClass.getName().equals(Function.class.getCanonicalName())){
                return true;
            } else {
                return false;
            }
        }

        // TODO look into generics
        if (typeUsage.describe().equals(this.getQualifiedName())){
            return true;
        }
        try {
            if (this.ctClass.getSuperclass() != null) {
                if (new JavassistClassDeclaration(this.ctClass.getSuperclass(), typeSolver).isAssignableBy(typeUsage)){
                    return true;
                }
            }
            for (CtClass interfaze : ctClass.getInterfaces()) {
                if (new JavassistClassDeclaration(interfaze, typeSolver).isAssignableBy(typeUsage)){
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
    public boolean isVariable() {
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
    public ReferenceTypeUsage getSuperClass() {
        try {
            if (ctClass.getSuperclass() == null) {
                throw new UnsupportedOperationException();
            }
            return new ReferenceTypeUsage(new JavassistClassDeclaration(ctClass.getSuperclass(), typeSolver).asClass(), typeSolver);
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public List<InterfaceDeclaration> getInterfaces() {
        throw new UnsupportedOperationException();
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
    public List<TypeParameter> getTypeParameters() {
        if (null == ctClass.getGenericSignature()) {
            return Collections.emptyList();
        } else {
            try {
                SignatureAttribute.ClassSignature classSignature = SignatureAttribute.toClassSignature(ctClass.getGenericSignature());
                return Arrays.<SignatureAttribute.TypeParameter>stream(classSignature.getParameters()).map((tp)->new JavassistTypeParameter(tp, true, typeSolver)).collect(Collectors.toList());
            } catch (BadBytecode badBytecode) {
                throw new RuntimeException(badBytecode);
            }
        }
    }
}
