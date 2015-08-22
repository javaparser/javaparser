package me.tomassetti.symbolsolver.model.typesolvers;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import me.tomassetti.symbolsolver.JavaParserFacade;
import me.tomassetti.symbolsolver.javaparser.Navigator;
import me.tomassetti.symbolsolver.model.SymbolReference;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.javaparser.JavaParserFactory;
import me.tomassetti.symbolsolver.model.javaparser.UnsolvedSymbolException;
import me.tomassetti.symbolsolver.model.javaparser.declarations.JavaParserClassDeclaration;

import java.io.File;
import java.io.IOException;

/**
 * @author Federico Tomassetti
 */
public class JavaParserTypeSolver implements TypeSolver {

    private File srcDir;

    public JavaParserTypeSolver(File srcDir) {
        this.srcDir = srcDir;
    }

    private String simpleName(String name){
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
        File srcFile = new File(srcDir.getAbsolutePath() +"/"+ name.replaceAll("\\.", "/") + ".java");
        if (srcFile.exists()) {
            try {
                CompilationUnit compilationUnit = JavaParser.parse(srcFile);
                ClassOrInterfaceDeclaration classOrInterfaceDeclaration = Navigator.demandClassOrInterface(compilationUnit, simpleName(name));
                TypeDeclaration typeDeclaration = JavaParserFacade.get(this).getTypeDeclaration(classOrInterfaceDeclaration);
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
