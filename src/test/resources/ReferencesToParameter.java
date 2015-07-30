package samples;

import com.github.javaparser.ast.expr.AnnotationExpr;

class ReferenceToParameter extends AnnotationExpr {

    public void aMethod(int foo){
        System.out.println(foo);
    }

}
