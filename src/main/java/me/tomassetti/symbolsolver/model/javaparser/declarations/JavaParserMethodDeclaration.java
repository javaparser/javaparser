package me.tomassetti.symbolsolver.model.javaparser.declarations;

import com.github.javaparser.ast.Node;
import me.tomassetti.symbolsolver.JavaParserFacade;
import me.tomassetti.symbolsolver.model.Context;
import me.tomassetti.symbolsolver.model.TypeParameter;
import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ParameterDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.javaparser.JavaParserFactory;
import me.tomassetti.symbolsolver.model.usages.MethodUsage;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;
import me.tomassetti.symbolsolver.model.usages.TypeUsageOfTypeDeclaration;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * Created by federico on 17/08/15.
 */
public class JavaParserMethodDeclaration implements MethodDeclaration {

    private com.github.javaparser.ast.body.MethodDeclaration wrappedNode;

    public JavaParserMethodDeclaration(com.github.javaparser.ast.body.MethodDeclaration wrappedNode) {
        this.wrappedNode = wrappedNode;
    }

    @Override
    public TypeDeclaration declaringType() {
        throw new UnsupportedOperationException();
    }

    @Override
    public TypeDeclaration getReturnType(TypeSolver typeSolver) {
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
        return new JavaParserParameterDeclaration(wrappedNode.getParameters().get(i));
    }

    @Override
    public MethodUsage getUsage(Node node) {
        throw new UnsupportedOperationException();
    }

    @Override
    public MethodUsage resolveTypeVariables(Context context, TypeSolver typeSolver) {
        TypeUsage returnType = replaceTypeParams(new TypeUsageOfTypeDeclaration(new JavaParserMethodDeclaration(wrappedNode).getReturnType(typeSolver)), typeSolver, context);
        List<TypeUsage> params = new ArrayList<>();
        for (int i=0;i<wrappedNode.getParameters().size();i++){
            TypeUsage replaced = replaceTypeParams(new TypeUsageOfTypeDeclaration(new JavaParserMethodDeclaration(wrappedNode).getParam(i).getType(typeSolver)), typeSolver, context);
            params.add(replaced);
        }
        return new MethodUsage(new JavaParserMethodDeclaration(wrappedNode), params, returnType);
    }

    @Override
    public Context getContext() {
        return JavaParserFactory.getContext(wrappedNode);
    }

    private Optional<TypeUsage> typeParamByName(String name, TypeSolver typeSolver, Context context){
        int i =  0;
        for (com.github.javaparser.ast.TypeParameter tp : wrappedNode.getTypeParameters()){
            if (tp.getName().equals(name)) {
                TypeUsage typeUsage = JavaParserFacade.get(typeSolver).convertToUsage( this.wrappedNode.getParameters().get(i).getType(), context);
                return Optional.of(typeUsage);
            }
            i++;
        }
        return Optional.empty();
    }

    private TypeUsage replaceTypeParams(TypeUsage typeUsage, TypeSolver typeSolver, Context context){
        if (typeUsage.isTypeVariable()) {
            TypeParameter typeParameter = typeUsage.asTypeParameter();
            if (typeParameter.declaredOnClass()) {
                Optional<TypeUsage> typeParam = typeParamByName(typeParameter.getName(), typeSolver, context);
                if (typeParam.isPresent()) {
                    typeUsage = typeParam.get();
                }
            }
        }

        for (int i=0; i<typeUsage.parameters().size(); i++) {
            TypeUsage replaced = replaceTypeParams(typeUsage.parameters().get(i), typeSolver, context);
            // Identity comparison on purpose
            if (replaced != typeUsage.parameters().get(i)) {
                typeUsage = typeUsage.replaceParam(i, replaced);
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
    public boolean isType() {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<TypeParameter> getTypeParameters() {
        throw new UnsupportedOperationException();
    }
}
