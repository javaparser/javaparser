package me.tomassetti.symbolsolver.resolution.typesolvers;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import me.tomassetti.symbolsolver.javaparser.Navigator;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.resolution.SymbolReference;
import me.tomassetti.symbolsolver.resolution.TypeSolver;
import me.tomassetti.symbolsolver.resolution.javaparser.JavaParserFacade;

import java.io.File;
import java.io.IOException;
import java.util.Optional;

/**
 * @author Federico Tomassetti
 */
public class JavaParserTypeSolver implements TypeSolver {

    private File srcDir;

    private TypeSolver parent;

    public JavaParserTypeSolver(File srcDir) {
        this.srcDir = srcDir;
    }

    @Override
    public String toString() {
        return "JavaParserTypeSolver{" +
                "srcDir=" + srcDir +
                ", parent=" + parent +
                '}';
    }

    @Override
    public TypeSolver getParent() {
        return parent;
    }

    @Override
    public void setParent(TypeSolver parent) {
        this.parent = parent;
    }

    private String simpleName(String name) {
        int index = name.lastIndexOf('.');
        if (index == -1) {
            return name;
        } else {
            return name.substring(index + 1);
        }
    }

    @Override
    public SymbolReference<TypeDeclaration> tryToSolveType(String name) {
        // TODO support internal classes
        // TODO support enums
        // TODO support interfaces
        File srcFile = new File(srcDir.getAbsolutePath() + "/" + name.replaceAll("\\.", "/") + ".java");
        if (srcFile.exists()) {
            try {
                CompilationUnit compilationUnit = JavaParser.parse(srcFile);
                Optional<com.github.javaparser.ast.body.TypeDeclaration> astTypeDeclaration = Navigator.findType(compilationUnit, simpleName(name));
                if (!astTypeDeclaration.isPresent()) {
                    return SymbolReference.unsolved(TypeDeclaration.class);
                }
                TypeDeclaration typeDeclaration = JavaParserFacade.get(this).getTypeDeclaration(astTypeDeclaration.get());
                return SymbolReference.solved(typeDeclaration);
            } catch (ParseException e) {
                throw new RuntimeException(e);
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        } else {
            return SymbolReference.unsolved(TypeDeclaration.class);
        }
    }

}
