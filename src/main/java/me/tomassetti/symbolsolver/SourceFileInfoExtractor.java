package me.tomassetti.symbolsolver;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.stmt.Statement;
import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;



import me.tomassetti.symbolsolver.model.usages.TypeUsage;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;




/**
 * It print information extracted from a source file. It is mainly intended as an example usage of JavaSymbolSolver.
 */
public class SourceFileInfoExtractor {

    private TypeSolver typeSolver;

    private int ok = 0;
    private int ko = 0;
    private int unsupported = 0;

    public void setPrintFileName(boolean printFileName) {
        this.printFileName = printFileName;
    }

    private boolean printFileName = true;

    public void clear() {
        ok = 0;
        ko = 0;
        unsupported = 0;
    }

    public void setOut(PrintStream out) {
        this.out = out;
    }

    public void setErr(PrintStream err) {
        this.err = err;
    }

    public int getOk() {
        return ok;

    }

    public int getUnsupported() {
        return unsupported;
    }

    public int getKo() {
        return ko;
    }

    private PrintStream out = System.out;
    private PrintStream err = System.err;

    private void solveTypeDecl(ClassOrInterfaceDeclaration node) {
        TypeDeclaration typeDeclaration = JavaParserFacade.get(typeSolver).getTypeDeclaration(node);
        if (typeDeclaration.isClass()) {
            out.println("\n[ Class "+ typeDeclaration.getQualifiedName() + " ]");
            for (TypeDeclaration sc : typeDeclaration.asClass().getAllSuperClasses(typeSolver)) {
                out.println("  superclass: " + sc.getQualifiedName());
            }
            for (TypeDeclaration sc : typeDeclaration.asClass().getAllInterfaces(typeSolver)) {
                out.println("  interface: " + sc.getQualifiedName());
            }
        }
    }

    private void solve(Node node) {
        if (node instanceof ClassOrInterfaceDeclaration) {
            solveTypeDecl((ClassOrInterfaceDeclaration)node);
        } else if (node instanceof Expression) {
            if ((node.getParentNode() instanceof ImportDeclaration) || (node.getParentNode() instanceof Expression)
                    || (node.getParentNode() instanceof MethodDeclaration)
                    || (node.getParentNode() instanceof PackageDeclaration)) {
                // skip
            } else if ((node.getParentNode() instanceof Statement) || (node.getParentNode() instanceof VariableDeclarator)){
                try {
                    TypeUsage ref = JavaParserFacade.get(typeSolver).getType(node);
                    out.println("  Line " + node.getBeginLine() + ") " + node + " ==> " + ref.prettyPrint());
                    ok++;
                } catch (UnsupportedOperationException upe){
                    unsupported++;
                    err.println(upe.getMessage());
                } catch (RuntimeException re){
                    ko++;
                    err.println(re.getMessage());
                }
            }
        }
        for (Node child : node.getChildrenNodes()){
            solve(child);
        }
    }

    public void solve(File file) throws IOException, ParseException {
        if (file.isDirectory()) {
            for (File f : file.listFiles()){
                solve(f);
            }
        } else {
            if (file.getName().endsWith(".java")) {
                if (printFileName) {
                    out.println("- parsing " + file.getAbsolutePath());
                }
                CompilationUnit cu = JavaParser.parse(file);
                solve(cu);
            }
        }
    }

    public void setTypeSolver(TypeSolver typeSolver) {
        this.typeSolver = typeSolver;
    }

}
