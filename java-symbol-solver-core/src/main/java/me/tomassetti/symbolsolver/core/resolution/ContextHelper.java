package me.tomassetti.symbolsolver.core.resolution;

import me.tomassetti.symbolsolver.javaparsermodel.declarations.JavaParserEnumDeclaration;
import me.tomassetti.symbolsolver.javaparsermodel.declarations.JavaParserMethodDeclaration;
import me.tomassetti.symbolsolver.javassistmodel.JavassistMethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.usages.MethodUsage;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;
import me.tomassetti.symbolsolver.reflectionmodel.ReflectionMethodDeclaration;

import java.util.List;

public class ContextHelper {

    static MethodUsage resolveTypeVariables(Context context, MethodDeclaration methodDeclaration, List<Type> parameterTypes) {
        if (methodDeclaration instanceof JavaParserMethodDeclaration) {
            return ((JavaParserMethodDeclaration)methodDeclaration).resolveTypeVariables(context, parameterTypes);
        } else if (methodDeclaration instanceof JavassistMethodDeclaration) {
            return ((JavassistMethodDeclaration)methodDeclaration).resolveTypeVariables(context, parameterTypes);
        } else if (methodDeclaration instanceof JavaParserEnumDeclaration.ValuesMethod) {
            return ((JavaParserEnumDeclaration.ValuesMethod)methodDeclaration).resolveTypeVariables(context, parameterTypes);
        } else if (methodDeclaration instanceof ReflectionMethodDeclaration) {
            return ((ReflectionMethodDeclaration)methodDeclaration).resolveTypeVariables(context, parameterTypes);
        } else {
            throw new UnsupportedOperationException();
        }
    }
}
