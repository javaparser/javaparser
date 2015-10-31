package me.tomassetti.symbolsolver.model.typesystem;

import me.tomassetti.symbolsolver.resolution.*;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.resolution.javaparser.LambdaArgumentTypeUsagePlaceholder;
import me.tomassetti.symbolsolver.resolution.javaparser.declarations.JavaParserTypeVariableDeclaration;
import me.tomassetti.symbolsolver.resolution.reflection.ReflectionClassDeclaration;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

public class ReferenceTypeUsage implements TypeUsage {

    private TypeDeclaration typeDeclaration;
    private List<TypeUsage> typeParameters;
    private TypeSolver typeSolver;

    public ReferenceTypeUsage asReferenceTypeUsage() {
        return this;
    }

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

    public ReferenceTypeUsage(TypeDeclaration typeDeclaration, TypeSolver typeSolver) {
        this(typeDeclaration, deriveParams(typeDeclaration), typeSolver);
        if (this.typeDeclaration.isTypeVariable()) {
            throw new IllegalArgumentException();
        }
        this.typeSolver = typeSolver;
    }

    private static List<TypeUsage> deriveParams(TypeDeclaration typeDeclaration) {
        return typeDeclaration.getTypeParameters().stream().map((tp)->new TypeParameterUsage(tp)).collect(Collectors.toList());
    }

    public boolean isEnum() {
        return typeDeclaration.isEnum();
    }

    public ReferenceTypeUsage(TypeDeclaration typeDeclaration, List<TypeUsage> typeParameters, TypeSolver typeSolver) {
        this.typeDeclaration = typeDeclaration;
        this.typeParameters = typeParameters;
        if (this.typeDeclaration.isTypeVariable()) {
            throw new IllegalArgumentException();
        }
        this.typeSolver = typeSolver;
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
    public boolean isReferenceType() {
        return true;
    }

    @Override
    public String toString() {
        return "ReferenceTypeUsage{" +
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
                typeParameters.add(new ReferenceTypeUsage(new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver));
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
    
    public Optional<Value> getField(String name, TypeSolver typeSolver) {
        if (!typeDeclaration.hasField(name)){
            return Optional.empty();
        }
        //Qui succede che getField avrebbe il tipo E. Devo vedere se io ho tipi da sostituire.



        TypeUsage typeUsage = typeDeclaration.getField(name).getType(typeSolver);
        //TypeUsage typeUsage = new TypeUsageOfTypeDeclaration(typeOfField);

        //ora io dovrei capire che mi ha restituito una variabile che si riferisce alla classe
        //rappresentata da THIS. Per capirlo potremmo associare piu' info alle TypeVariable,
        //mettendo dove sono state dichiarate


        // Mi pare risolviamo nel punto sbagliato, dovrebbe essere
        typeUsage = replaceTypeParams(typeUsage);

        return Optional.of(new Value(typeUsage, name, true));
    }

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

    /**
     * Create a copy of the value with the type parameter changed.
     * @param i
     * @param replaced
     * @return
     */
    public TypeUsage replaceParam(int i, TypeUsage replaced) {
        ArrayList<TypeUsage> typeParametersCorrected = new ArrayList<>(typeParameters);
        typeParametersCorrected.set(i, replaced);
        return new ReferenceTypeUsage(typeDeclaration, typeParametersCorrected, typeSolver);
    }

    @Override
    public TypeUsage replaceParam(String name, TypeUsage replaced) {
        List<TypeUsage> newParams = typeParameters.stream().map((tp)->tp.replaceParam(name, replaced)).collect(Collectors.toList());
        if (typeParameters.equals(newParams)) {
            return this;
        } else {
            return new ReferenceTypeUsage(typeDeclaration, newParams, typeSolver);
        }
    }

    public List<ReferenceTypeUsage> getAllAncestors() {
        return typeDeclaration.getAllAncestors();
    }

    public TypeUsage replaceTypeParams(TypeUsage typeUsage){
        if (typeUsage.isTypeVariable()) {
            TypeParameter typeParameter = typeUsage.asTypeParameter();
            if (typeParameter.declaredOnClass()) {
                Optional<TypeUsage> typeParam = typeParamByName(typeParameter.getName());
                if (typeParam.isPresent()) {
                    typeUsage = typeParam.get();
                }
            }
        }

        if (typeUsage.isReferenceType()) {
            for (int i = 0; i < typeUsage.asReferenceTypeUsage().parameters().size(); i++) {
                TypeUsage replaced = replaceTypeParams(typeUsage.asReferenceTypeUsage().parameters().get(i));
                // Identity comparison on purpose
                if (replaced != typeUsage.asReferenceTypeUsage().parameters().get(i)) {
                    typeUsage = typeUsage.asReferenceTypeUsage().replaceParam(i, replaced);
                }
            }
        }

        return typeUsage;
    }

    @Override
    public String describe() {
        StringBuffer sb = new StringBuffer();
        sb.append(typeDeclaration.getQualifiedName());
        if (parameters().size() > 0){
            sb.append("<");
            boolean first = true;
            for (TypeUsage param : parameters()) {
                if (first) {
                    first = false;
                } else {
                    sb.append(", ");
                }
                sb.append(param.describe());
            }
            sb.append(">");
        }
        return sb.toString();
    }

    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver) {
        return typeDeclaration.solveMethod(name, parameterTypes, typeSolver);
    }

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
    public boolean isAssignableBy(TypeUsage other) {
        if (other instanceof NullTypeUsage){
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
            return this.getQualifiedName().equals(Predicate.class.getCanonicalName()) || this.getQualifiedName().equals(Function.class.getCanonicalName());
        } else if (other instanceof ReferenceTypeUsage) {
            ReferenceTypeUsage otherTUOTD = (ReferenceTypeUsage) other;
            return typeDeclaration.isAssignableBy(otherTUOTD.typeDeclaration);

        } else if (other.isTypeVariable()) {
            // TODO look bounds...
            return true;
        } else {
            return false;
        }
    }

    private boolean isCorrespondingBoxingType(String typeName) {
        switch (typeName) {
            case "boolean":
                return getQualifiedName().equals(Boolean.class.getCanonicalName());
            case "char":
                return getQualifiedName().equals(Character.class.getCanonicalName());
            case "byte":
                return getQualifiedName().equals(Byte.class.getCanonicalName());
            case "short":
                return getQualifiedName().equals(Short.class.getCanonicalName());
            case "int":
                return getQualifiedName().equals(Integer.class.getCanonicalName());
            case "long":
                return getQualifiedName().equals(Long.class.getCanonicalName());
            case "float":
                return getQualifiedName().equals(Float.class.getCanonicalName());
            case "double":
                return getQualifiedName().equals(Double.class.getCanonicalName());
            default:
                throw new UnsupportedOperationException(typeName);
        }
    }

    public String getQualifiedName() {
        return typeDeclaration.getQualifiedName();
    }

}
