package me.tomassetti.symbolsolver.resolution.typesolvers;

import javassist.ClassPool;
import javassist.CtClass;
import javassist.NotFoundException;
import me.tomassetti.symbolsolver.javassistmodel.JavassistFactory;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.javaparsermodel.UnsolvedSymbolException;

import java.io.IOException;
import java.io.InputStream;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.Map;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;

public class JarTypeSolver implements TypeSolver {

    private TypeSolver parent;
    private Map<String, ClasspathElement> classpathElements = new HashMap<>();
    private ClassPool classPool = new ClassPool(false);

    public JarTypeSolver(String pathToJar) throws IOException {
        try {
            classPool.appendClassPath(pathToJar);
            classPool.appendSystemPath();
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }
        JarFile jarFile = new JarFile(pathToJar);
        JarEntry entry = null;
        for (Enumeration<JarEntry> e = jarFile.entries(); e.hasMoreElements(); entry = e.nextElement()) {
            if (entry != null && !entry.isDirectory() && entry.getName().endsWith(".class")) {
                String name = entryPathToClassName(entry.getName());
                classpathElements.put(name, new ClasspathElement(jarFile, entry, name));
            }
        }
    }

    @Override
    public TypeSolver getParent() {
        return parent;
    }

    @Override
    public void setParent(TypeSolver parent) {
        this.parent = parent;
    }

    private String entryPathToClassName(String entryPath) {
        if (!entryPath.endsWith(".class")) {
            throw new IllegalStateException();
        }
        String className = entryPath.substring(0, entryPath.length() - ".class".length());
        className = className.replaceAll("/", ".");
        className = className.replaceAll("\\$", ".");
        return className;
    }

    @Override
    public SymbolReference<TypeDeclaration> tryToSolveType(String name) {
        try {
            if (classpathElements.containsKey(name)) {
                return SymbolReference.solved(JavassistFactory.toTypeDeclaration(classpathElements.get(name).toCtClass(), getRoot()));
            } else {
                return SymbolReference.unsolved(TypeDeclaration.class);
            }
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public TypeDeclaration solveType(String name) throws UnsolvedSymbolException {
        SymbolReference<TypeDeclaration> ref = tryToSolveType(name);
        if (ref.isSolved()) {
            return ref.getCorrespondingDeclaration();
        } else {
            throw new UnsolvedSymbolException(name);
        }
    }

    private class ClasspathElement {
        private JarFile jarFile;
        private JarEntry entry;
        private String path;

        public ClasspathElement(JarFile jarFile, JarEntry entry, String path) {
            this.jarFile = jarFile;
            this.entry = entry;
            this.path = path;
        }

        CtClass toCtClass() throws IOException {
            InputStream is = jarFile.getInputStream(entry);
            CtClass ctClass = classPool.makeClass(is);
            return ctClass;
        }
    }
}
