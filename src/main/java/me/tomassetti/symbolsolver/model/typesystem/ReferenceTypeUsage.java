package me.tomassetti.symbolsolver.model.typesystem;

import me.tomassetti.symbolsolver.model.*;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.javaparser.declarations.JavaParserTypeVariableDeclaration;
import me.tomassetti.symbolsolver.model.reflection.ReflectionClassDeclaration;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

/**
 * Created by federico on 31/07/15.
 */
public class ReferenceTypeUsage implements TypeUsage {

    private TypeDeclaration typeDeclaration;
    private List<TypeUsage> typeParameters;

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        ReferenceTypeUsage that = (ReferenceTypeUsage) o;

        if (!typeDeclaration.equals(that.typeDeclaration)) return false;
        if (!typeParameters.equals(that.typeParameters)) return false;

        return true;
    }

    @Override
    public int hashCode() {
        int result = typeDeclaration.hashCode();
        result = 31 * result + typeParameters.hashCode();
        return result;
    }

    public TypeDeclaration getTypeDeclaration() {
        return typeDeclaration;
    }

    public void setTypeDeclaration(TypeDeclaration typeDeclaration) {
        this.typeDeclaration = typeDeclaration;
        if (this.typeDeclaration.isTypeVariable()) {
            throw new IllegalArgumentException();
        }
    }

    public ReferenceTypeUsage(TypeDeclaration typeDeclaration) {
        this(typeDeclaration, deriveParams(typeDeclaration));
        if (this.typeDeclaration.isTypeVariable()) {
            throw new IllegalArgumentException();
        }
    }

    private static List<TypeUsage> deriveParams(TypeDeclaration typeDeclaration) {
        return typeDeclaration.getTypeParameters().stream().map((tp)->new TypeUsageOfTypeParameter(tp)).collect(Collectors.toList());
    }

    @Override
    public boolean isEnum() {
        return typeDeclaration.isEnum();
    }

    public ReferenceTypeUsage(TypeDeclaration typeDeclaration, List<TypeUsage> typeParameters) {
        this.typeDeclaration = typeDeclaration;
        this.typeParameters = typeParameters;
        if (this.typeDeclaration.isTypeVariable()) {
            throw new IllegalArgumentException();
        }
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
        List<TypeUsage> typeParameters = this.typeParameters;
        if (typeDeclaration.getTypeParameters().size() != typeParameters.size()){
            if (typeParameters.size() > 0) {
                throw new UnsupportedOperationException();
            }
            // type parameters not specified, default to Object
            typeParameters = new ArrayList<>();
            for (int i=0;i<typeDeclaration.getTypeParameters().size();i++){
                typeParameters.add(new ReferenceTypeUsage(new ReflectionClassDeclaration(Object.class)));
            }
        }
        int i =  0;
        for (TypeParameter tp : typeDeclaration.getTypeParameters()){
            if (tp.getName().equals(name)) {
                return Optional.of(typeParameters.get(i));
            }
            i++;
        }
        return Optional.empty();
    }

    @Override
    public Optional<Value> getField(String name, TypeSolver typeSolver) {
        if (!typeDeclaration.hasField(name, typeSolver)){
            return Optional.empty();
        }
        //Qui succede che getField avrebbe il tipo E. Devo vedere se io ho tipi da sostituire.



        TypeUsage typeUsage = typeDeclaration.getField(name, typeSolver).getType(typeSolver);
        //TypeUsage typeUsage = new TypeUsageOfTypeDeclaration(typeOfField);

        //ora io dovrei capire che mi ha restituito una variabile che si riferisce alla classe
        //rappresentata da THIS. Per capirlo potremmo associare piu' info alle TypeVariable,
        //mettendo dove sono state dichiarate


        // Mi pare risolviamo nel punto sbagliato, dovrebbe essere
        typeUsage = replaceTypeParams(typeUsage);

        return Optional.of(new Value(typeUsage, name, true));
    }

    @Override
    public Optional<MethodUsage> solveMethodAsUsage(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver, Context invokationContext) {
        Optional<MethodUsage> ref = typeDeclaration.solveMethodAsUsage(name, parameterTypes, typeSolver, invokationContext, typeParameters);
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
        return new ReferenceTypeUsage(typeDeclaration, typeParametersCorrected);
    }

    @Override
    public TypeUsage replaceParam(String name, TypeUsage replaced) {
        List<TypeUsage> newParams = typeParameters.stream().map((tp)->tp.replaceParam(name, replaced)).collect(Collectors.toList());
        if (typeParameters.equals(newParams)) {
            return this;
        } else {
            return new ReferenceTypeUsage(typeDeclaration, newParams);
        }
    }

    @Override
    public List<ReferenceTypeUsage> getAllAncestors(TypeSolver typeSolver) {
        return typeDeclaration.getAllAncestors(typeSolver);
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
        if (other instanceof NullTypeUsage){
            return !this.isPrimitive();
        }
        // consider boxing
        if (other.isPrimitive()) {
            if (this.getQualifiedName().equals(Object.class.getCanonicalName())) {
                return true;
            } else {
                return isCorrespondingBoxingType(other.getTypeName());
            }
        }
        if (other instanceof LambdaTypeUsagePlaceholder) {
            return this.getQualifiedName().equals(Predicate.class.getCanonicalName()) || this.getQualifiedName().equals(Function.class.getCanonicalName());
        } else if (other instanceof ReferenceTypeUsage) {
            ReferenceTypeUsage otherTUOTD = (ReferenceTypeUsage) other;
            return typeDeclaration.isAssignableBy(otherTUOTD.typeDeclaration, typeSolver);

        } else if (other.isTypeVariable()) {
            // TODO look bounds...
            return true;
        } else {
            return false;
        }
    }

    private boolean isCorrespondingBoxingType(String typeName) {
        switch (typeName) {
            case "char":
                return getQualifiedName().equals(Character.class.getCanonicalName());
            default:
                throw new UnsupportedOperationException(typeName);
        }
    }

    @Override
    public String getQualifiedName() {
        return typeDeclaration.getQualifiedName();
    }

    @Override
    public String prettyPrint() {
        return getTypeNameWithParams();
    }
}
