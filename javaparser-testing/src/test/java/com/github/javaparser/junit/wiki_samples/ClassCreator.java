package com.github.javaparser.junit.wiki_samples;

import java.util.EnumSet;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.StringLiteralExpr;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.type.ClassOrInterfaceType;

import static com.github.javaparser.ast.expr.NameExpr.*;
import static com.github.javaparser.ast.type.VoidType.*;
import static com.github.javaparser.utils.Utils.some;

public class ClassCreator {

    public static void main(String[] args) throws Exception {
        // creates the compilation unit
        CompilationUnit cu = createCU();

        // prints the created compilation unit
        System.out.println(cu.toString());
    }

    /**
     * creates the compilation unit
     */
    private static CompilationUnit createCU() {
        CompilationUnit cu = new CompilationUnit();
        // set the package
        cu.setPackage(new PackageDeclaration(name("java.parser.test")));

        // create the type declaration 
        ClassOrInterfaceDeclaration type = cu.addClass("GeneratedClass");
        // create a method
		EnumSet<Modifier> modifiers = EnumSet.of(Modifier.PUBLIC);
		MethodDeclaration method = new MethodDeclaration(modifiers, VOID_TYPE, "main");
		modifiers.add(Modifier.STATIC);
		method.setModifiers(modifiers);
        type.addMember(method);

        // add a parameter to the method
        Parameter param = Parameter.create(new ClassOrInterfaceType("String"), "args");
        param.setVarArgs(true);
        method.addParameter(param);

        // add a body to the method
        BlockStmt block = new BlockStmt();
        method.setBody(some(block));

        // add a statement do the method body
        NameExpr clazz = new NameExpr("System");
        FieldAccessExpr field = new FieldAccessExpr(clazz, "out");
        MethodCallExpr call = new MethodCallExpr(some(field), "println");
        call.addArgument(new StringLiteralExpr("Hello World!"));
        block.addStatement(call);

        return cu;
    }
}