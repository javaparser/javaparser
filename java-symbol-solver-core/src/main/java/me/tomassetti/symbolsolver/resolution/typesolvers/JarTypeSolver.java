package me.tomassetti.symbolsolver.resolution.typesolvers;

import javassist.ClassPool;
import javassist.CtClass;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.resolution.javaparser.UnsolvedSymbolException;
import me.tomassetti.symbolsolver.javassistmodel.JavassistClassDeclaration;

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

    public JarTypeSolver(String pathToJar) throws IOException {
        JarFile jarFile = new JarFile(pathToJar);
        JarEntry entry = null;
        for (Enumeration<JarEntry> e = jarFile.entries(); e.hasMoreElements(); entry = e.nextElement()) {
            if (entry != null && !entry.isDirectory() && entry.getName().endsWith(".class")) {
                String name = entryPathToClassName(entry.getName());
                classpathElements.put(name, new ClasspathElement(jarFile, entry, name));
            }
        }
    }

    /*
    (defrecord ClasspathElement [resource path contentAsStreamThunk])

(defn- jarEntryToClasspathElement [jarFile jarEntry]
  (let [name (.getName jarEntry)
        content (fn [] (.getInputStream jarFile jarEntry))]
    (ClasspathElement. jarFile name content)))

(defn getElementsEntriesInJar
  "Return a set of ClasspathElements"
  [pathToJarFile]
  (let [url (URLDecoder/decode pathToJarFile "UTF-8")
        jarfile (new JarFile url)
        entries (enumeration-seq (.entries jarfile))
        entries' (filter (fn [e] (not (.isDirectory e))) entries)]
    (map (partial jarEntryToClasspathElement jarfile) entries')))

(defn getClassesEntriesInJar
  "Return a set of ClasspathElements"
  [pathToJarFile]
  (filter (fn [e] (.endsWith (.path e) ".class")) (getElementsEntriesInJar pathToJarFile)))

(defn pathToTypeName [path]
  (if (.endsWith path ".class")
    (let [path' (.substring path 0 (- (.length path) 6))
          path'' (clojure.string/replace path' #"/" ".")
          path''' (clojure.string/replace path'' "$" ".")]
      path''')
    (throw (IllegalArgumentException. "Path not ending with .class"))))

(defn findEntry
  "return the ClasspathElement corresponding to the given name, or nil"
  [typeName classEntries]
  (first (filter (fn [e] (= typeName (pathToTypeName (.path e)))) classEntries)))

(defn findType
  "return the CtClass corresponding to the given name, or nil"
  [typeName classEntries]
  (let [entry (findEntry typeName classEntries)
        classPool (ClassPool/getDefault)]
    (when entry
      (.makeClass classPool ((.contentAsStreamThunk entry))))))

     */

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
                return SymbolReference.solved(new JavassistClassDeclaration(classpathElements.get(name).toCtClass(), getRoot()));
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
            ClassPool classPool = ClassPool.getDefault();
            CtClass ctClass = classPool.makeClass(is);
            return ctClass;
        }
    }
}
