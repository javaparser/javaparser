package me.tomassetti.symbolsolver.model.javaparser.declarations;

import com.github.javaparser.ast.body.VariableDeclarator;
import me.tomassetti.symbolsolver.JavaParserFacade;
import me.tomassetti.symbolsolver.model.FieldDeclaration;
import me.tomassetti.symbolsolver.model.TypeParameter;
import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;
import me.tomassetti.symbolsolver.model.usages.TypeUsageOfTypeDeclaration;

import java.util.Optional;

/**
 * Created by federico on 04/08/15.
 */
public class JavaParserFieldDeclaration implements FieldDeclaration {

    private VariableDeclarator variableDeclarator;
    private com.github.javaparser.ast.body.FieldDeclaration fieldDeclaration;

    public JavaParserFieldDeclaration(VariableDeclarator variableDeclarator) {
        this.variableDeclarator = variableDeclarator;
        if (!(variableDeclarator.getParentNode() instanceof com.github.javaparser.ast.body.FieldDeclaration)){
            throw new IllegalStateException();
        }
        this.fieldDeclaration = (com.github.javaparser.ast.body.FieldDeclaration)variableDeclarator.getParentNode();
    }

    @Override
    public TypeDeclaration asTypeDeclaration() {
        throw new UnsupportedOperationException();
    }

    @Override
    public TypeUsage getTypeUsage(TypeSolver typeSolver) {
        return new JavaParserFacade(typeSolver).convertToUsage(fieldDeclaration.getType(), fieldDeclaration);
        /*TypeUsage typeUsage = new TypeUsageOfTypeDeclaration(typeDeclaration);
        if (!typeUsage.parameters().isEmpty()) {
            throw new UnsupportedOperationException(typeUsage.toString()+" "+fieldDeclaration.getType());
        }
        return typeUsage;*/
    }

    /*private TypeUsage replaceTypeParams(TypeUsage typeUsage){
        System.out.println("GOT "+typeUsage);
        if (typeUsage.isTypeVariable()) {
            System.out.println("  is type variable");
            TypeParameter typeParameter = typeUsage.asTypeParameter();
            if (typeParameter.declaredOnClass()) {
                System.out.println("  declared on class");
                System.out.println("  type param name "+typeParameter.getName());
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

        System.out.println("TRANSFORMED IN "+typeUsage);

        return typeUsage;
    }*/


    @Override
    public TypeDeclaration getType(TypeSolver typeSolver) {
        return new JavaParserFacade(typeSolver).convert(fieldDeclaration.getType(), fieldDeclaration);
    }

    @Override
    public String getName() {
        throw new UnsupportedOperationException();
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
}
