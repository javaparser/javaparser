package me.tomassetti.symbolsolver.model.usages;

import me.tomassetti.symbolsolver.model.*;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.javaparser.declarations.JavaParserTypeVariableDeclaration;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * Created by federico on 31/07/15.
 */
public class TypeUsageOfTypeDeclaration implements TypeUsage {

    private TypeDeclaration typeDeclaration;
    private List<TypeUsage> typeParameters;

    public TypeUsageOfTypeDeclaration(TypeDeclaration typeDeclaration) {
        this(typeDeclaration, deriveParams(typeDeclaration));
    }

    private static List<TypeUsage> deriveParams(TypeDeclaration typeDeclaration) {
        return typeDeclaration.getTypeParameters().stream().map((tp)->new TypeUsageOfTypeParameter(tp)).collect(Collectors.toList());
    }

    public TypeUsageOfTypeDeclaration(TypeDeclaration typeDeclaration, List<TypeUsage> typeParameters) {
        this.typeDeclaration = typeDeclaration;
        this.typeParameters = typeParameters;
    }

    @Override
    public boolean isArray() {
        return false;
    }

    @Override
    public boolean isPrimitive() {
        return false;
    }

    @Override
    public Optional<TypeUsage> parameterByName(String name) {
        int i=0;
        for (TypeParameter tp : typeDeclaration.getTypeParameters()) {
            if (tp.getName().equals(name)) {
                return Optional.of(typeParameters.get(i));
            }
            i++;
        }
        return Optional.empty();
    }

    @Override
    public boolean isReferenceType() {
        return true;
    }

    @Override
    public String toString() {
        return "TypeUsageOfTypeDeclaration{" +
                "declaration=" + typeDeclaration +
                ", typeParameters=" + typeParameters +
                '}';
    }

    private Optional<TypeUsage> typeParamByName(String name){
        int i =  0;
        for (TypeParameter tp : typeDeclaration.getTypeParameters()){
            if (tp.getName().equals(name)) {
                return Optional.of(this.typeParameters.get(i));
            }
            i++;
        }
        return Optional.empty();
    }

    @Override
    public Optional<Value> getField(String name, TypeSolver typeSolver) {
        if (!typeDeclaration.hasField(name)){
            return Optional.empty();
        }
        TypeUsage typeUsage = typeDeclaration.getField(name).getType(typeSolver);
        //TypeUsage typeUsage = new TypeUsageOfTypeDeclaration(typeOfField);

        //ora io dovrei capire che mi ha restituito una variabile che si riferisce alla classe
        //rappresentata da THIS. Per capirlo potremmo associare piu' info alle TypeVariable,
        //mettendo dove sono state dichiarate


        typeUsage = replaceTypeParams(typeUsage);

        return Optional.of(new Value(typeUsage, name, true));
    }

    @Override
    public Optional<MethodUsage> solveMethodAsUsage(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver, Context invokationContext) {
        Optional<MethodUsage> ref = typeDeclaration.solveMethodAsUsage(name, parameterTypes, typeSolver, invokationContext);
        if (ref.isPresent()) {
            MethodUsage methodUsage = ref.get();
            TypeUsage returnType = replaceTypeParams(methodUsage.returnType());
            if (returnType != methodUsage.returnType()){
                methodUsage = methodUsage.replaceReturnType(returnType);
            }
            for (int i=0;i<methodUsage.getParamTypes().size();i++){
                TypeUsage replaced = replaceTypeParams(methodUsage.getParamTypes().get(i));
                methodUsage = methodUsage.replaceParamType(i, replaced);
            }
            return Optional.of(methodUsage);
        } else {
            return ref;
        }
    }

    @Override
    public Optional<TypeUsage> solveGenericType(String name) {
        int i=0;
        for (TypeParameter tp :typeDeclaration.getTypeParameters()){
            if (tp.getName().equals(name)){
                return Optional.of(this.typeParameters.get(i));
            }
            i++;
        }
        return Optional.empty();
    }

    @Override
    public TypeUsage replaceParam(int i, TypeUsage replaced) {
        ArrayList<TypeUsage> typeParametersCorrected = new ArrayList<>(typeParameters);
        typeParametersCorrected.set(i, replaced);
        return new TypeUsageOfTypeDeclaration(typeDeclaration, typeParametersCorrected);
    }

    private TypeUsage replaceTypeParams(TypeUsage typeUsage){
        if (typeUsage.isTypeVariable()) {
            TypeParameter typeParameter = typeUsage.asTypeParameter();
            if (typeParameter.declaredOnClass()) {
                Optional<TypeUsage> typeParam = typeParamByName(typeParameter.getName());
                if (typeParam.isPresent()) {
                    typeUsage = typeParam.get();
                }
            }
        }

        for (int i=0; i<typeUsage.parameters().size(); i++) {
            TypeUsage replaced = replaceTypeParams(typeUsage.parameters().get(i));
            // Identity comparison on purpose
            if (replaced != typeUsage.parameters().get(i)) {
                typeUsage = typeUsage.replaceParam(i, replaced);
            }
        }

        return typeUsage;
    }

    @Override
    public String getTypeName() {
        return typeDeclaration.getQualifiedName();
    }

    @Override
    public TypeUsage getBaseType() {
        throw new UnsupportedOperationException();
    }

    @Override
    public Context getContext() {
        throw new UnsupportedOperationException();
    }

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver) {
        return typeDeclaration.solveMethod(name, parameterTypes, typeSolver);
    }

    @Override
    public List<TypeUsage> parameters() {
        return typeParameters;
    }

    @Override
    public TypeParameter asTypeParameter() {
        if (this.typeDeclaration instanceof JavaParserTypeVariableDeclaration){
            JavaParserTypeVariableDeclaration javaParserTypeVariableDeclaration = (JavaParserTypeVariableDeclaration)this.typeDeclaration;
            return javaParserTypeVariableDeclaration.asTypeParameter();
        }
        throw new UnsupportedOperationException(this.typeDeclaration.getClass().getCanonicalName());
    }

    @Override
    public boolean isTypeVariable() {
        return typeDeclaration.isTypeVariable();
    }

    @Override
    public boolean isAssignableBy(TypeUsage other, TypeSolver typeSolver) {
        if (other instanceof TypeUsageOfTypeDeclaration) {
            TypeUsageOfTypeDeclaration otherTUOTD = (TypeUsageOfTypeDeclaration)other;
            return typeDeclaration.isAssignableBy(otherTUOTD.typeDeclaration, typeSolver);
        } else {
            return false;
        }
    }

    @Override
    public String getQualifiedName() {
        return typeDeclaration.getQualifiedName();
    }
}
