package me.tomassetti.symbolsolver.resolution.typesolvers;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;

import me.tomassetti.symbolsolver.javaparser.Navigator;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFacade;

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

    @Override
    public SymbolReference<TypeDeclaration> tryToSolveType(String name) {
        // TODO support enums
        // TODO support interfaces
    	
    	String[] nameElements = name.split("\\.");
    	
    	for (int i = nameElements.length; i > 0; i--) {
        	String filePath = srcDir.getAbsolutePath();
        	for (int j = 0; j < i; j++) {
        		filePath += "/" + nameElements[j];
        	}
        	filePath += ".java";
        	
            File srcFile = new File(filePath);
            if (srcFile.exists()) {
                try {
                    String typeName = "";
                    for (int j = i - 1; j < nameElements.length; j++) {
                        if (j != i - 1)
                        {
                            typeName += ".";
                        }
                        typeName += nameElements[j];
                    }
                    CompilationUnit compilationUnit = JavaParser.parse(srcFile);
                    Optional<com.github.javaparser.ast.body.TypeDeclaration> astTypeDeclaration = Navigator.findType(compilationUnit, typeName);
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
            }
        }
    	
    	return SymbolReference.unsolved(TypeDeclaration.class);
    }

}
