package me.tomassetti.symbolsolver.javaparsermodel.contexts;

import me.tomassetti.symbolsolver.core.resolution.Context;
import me.tomassetti.symbolsolver.javaparsermodel.declarations.JavaParserEnumDeclaration;
import me.tomassetti.symbolsolver.javassistmodel.JavassistClassDeclaration;
import me.tomassetti.symbolsolver.javassistmodel.JavassistInterfaceDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.usages.MethodUsage;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;
import me.tomassetti.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import me.tomassetti.symbolsolver.reflectionmodel.ReflectionInterfaceDeclaration;

import java.lang.reflect.InvocationTargetException;
import java.util.List;
import java.util.Optional;

/**
 * Created by federico on 14/10/16.
 */
public class ContextHelper {

    public static Context getContext(TypeDeclaration typeDeclaration) {
        try {
            return (Context)typeDeclaration.getClass().getMethod("getContext").invoke(typeDeclaration);
        } catch (IllegalAccessException e) {
            throw new RuntimeException(e);
        } catch (InvocationTargetException e) {
            throw new RuntimeException(e);
        } catch (NoSuchMethodException e) {
            throw new RuntimeException(e);
        }
    }

    public static Optional<MethodUsage> solveMethodAsUsage(TypeDeclaration typeDeclaration, String name,
                                                     List<Type> parameterTypes, TypeSolver typeSolver,
                                                     Context invokationContext, List<Type> typeParameters) {
        if (typeDeclaration instanceof JavassistClassDeclaration) {
            return ((JavassistClassDeclaration) typeDeclaration).solveMethodAsUsage(name, parameterTypes, typeSolver, invokationContext, typeParameters);
        } else if (typeDeclaration instanceof JavassistInterfaceDeclaration) {
            return ((JavassistInterfaceDeclaration) typeDeclaration).solveMethodAsUsage(name, parameterTypes, typeSolver, invokationContext, typeParameters);
        }  else if (typeDeclaration instanceof JavaParserEnumDeclaration) {
            return ((JavaParserEnumDeclaration) typeDeclaration).solveMethodAsUsage(name, parameterTypes, typeSolver, invokationContext, typeParameters);
        } else  if (typeDeclaration instanceof ReflectionClassDeclaration) {
            return ((ReflectionClassDeclaration) typeDeclaration).solveMethodAsUsage(name, parameterTypes, typeSolver, invokationContext, typeParameters);
        } else if (typeDeclaration instanceof ReflectionInterfaceDeclaration) {
            return ((ReflectionInterfaceDeclaration) typeDeclaration).solveMethodAsUsage(name, parameterTypes, typeSolver, invokationContext, typeParameters);
        }
        return getContext(typeDeclaration).solveMethodAsUsage(name, parameterTypes, typeSolver);
    }

}
