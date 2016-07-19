package com.github.javaparser.junit;

import java.util.EnumSet;

import com.github.javaparser.ASTHelper;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Modifier;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.StringLiteralExpr;
import com.github.javaparser.ast.stmt.BlockStmt;

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
        cu.setPackage(new PackageDeclaration(ASTHelper.createNameExpr("java.parser.test")));

        // create the type declaration 
		ClassOrInterfaceDeclaration type = new ClassOrInterfaceDeclaration(EnumSet.of(Modifier.PUBLIC), false, "GeneratedClass");
        ASTHelper.addTypeDeclaration(cu, type);

        // create a method
		EnumSet<Modifier> modifiers = EnumSet.of(Modifier.PUBLIC);
		MethodDeclaration method = new MethodDeclaration(modifiers, ASTHelper.VOID_TYPE, "main");
		modifiers.add(Modifier.STATIC);
		method.setModifiers(modifiers);
        ASTHelper.addMember(type, method);

        // add a parameter to the method
        Parameter param = ASTHelper.createParameter(ASTHelper.createReferenceType("String", 0), "args");
        param.setVarArgs(true);
        ASTHelper.addParameter(method, param);

        // add a body to the method
        BlockStmt block = new BlockStmt();
        method.setBody(block);

        // add a statement do the method body
        NameExpr clazz = new NameExpr("System");
        FieldAccessExpr field = new FieldAccessExpr(clazz, "out");
        MethodCallExpr call = new MethodCallExpr(field, "println");
        ASTHelper.addArgument(call, new StringLiteralExpr("Hello World!"));
        ASTHelper.addStmt(block, call);

        return cu;
    }
}