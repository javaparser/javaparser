package me.tomassetti.examples;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.usages.typesystem.ReferenceType;
import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFacade;
import me.tomassetti.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import me.tomassetti.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;

public class PrintExpressionType {



    static class TypeCalculatorVisitor extends VoidVisitorAdapter<JavaParserFacade> {
        @Override
        public void visit(ReturnStmt n, JavaParserFacade javaParserFacade) {
            super.visit(n, javaParserFacade);
            //System.out.println(n.getExpr().toString() + " has type " + javaParserFacade.getType(n.getExpr()));
        }

        @Override
        public void visit(MethodCallExpr n, JavaParserFacade javaParserFacade) {
            super.visit(n, javaParserFacade);
            System.out.println(n.toString() + " has type " + javaParserFacade.getType(n).describe());
            if (javaParserFacade.getType(n).isReferenceType()) {
                for (ReferenceType ancestor : javaParserFacade.getType(n).asReferenceType().getAllAncestors()) {
                    //System.out.println("Ancestor " + ancestor.describe());
                }
            }
        }
    }

    public static void main(String[] args) throws FileNotFoundException, ParseException {
        TypeSolver typeSolver = new CombinedTypeSolver(new JreTypeSolver(), new JavaParserTypeSolver(new File("java-symbol-solver-examples/src/main/resources/someproject")));

        CompilationUnit agendaCu = JavaParser.parse(new FileInputStream(new File("java-symbol-solver-examples/src/main/resources/someproject/me/tomassetti/Agenda.java")));

        agendaCu.accept(new TypeCalculatorVisitor(), JavaParserFacade.get(typeSolver));

    }

}
