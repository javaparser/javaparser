package bdd.steps;

import japa.parser.ast.body.BodyDeclaration;
import japa.parser.ast.body.TypeDeclaration;

public class CommonSteps {

    public static BodyDeclaration getMemberByTypeAndPosition(TypeDeclaration typeDeclaration, int position,
                                                       Class<? extends BodyDeclaration> typeClass){
        int typeCount = 0;
        for(BodyDeclaration declaration : typeDeclaration.getMembers()){
            if(declaration.getClass().equals(typeClass)){
                if(typeCount == position){
                    return declaration;
                }
                typeCount++;
            }
        }
        throw new IllegalArgumentException("No member " + typeClass + " at position: " + position );
    }
}
