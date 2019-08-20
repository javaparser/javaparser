/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */
package com.github.javaparser.ast;

import com.github.javaparser.*;
import com.github.javaparser.ast.body.AnnotationDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.modules.ModuleDeclaration;
import com.github.javaparser.ast.nodeTypes.NodeWithName;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.CompilationUnitMetaModel;
import com.github.javaparser.metamodel.InternalProperty;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.OptionalProperty;
import com.github.javaparser.printer.PrettyPrinter;
import com.github.javaparser.utils.ClassUtils;
import com.github.javaparser.utils.CodeGenerationUtils;
import com.github.javaparser.utils.Utils;
import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;
import static com.github.javaparser.JavaToken.Kind.EOF;
import static com.github.javaparser.Providers.UTF8;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.Range.range;
import static com.github.javaparser.StaticJavaParser.parseImport;
import static com.github.javaparser.StaticJavaParser.parseName;
import static com.github.javaparser.ast.Modifier.createModifierList;
import static com.github.javaparser.utils.CodeGenerationUtils.subtractPaths;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.Generated;

/**
 * <p>
 * This class represents the entire compilation unit. Each java file denotes a
 * compilation unit.
 * </p>
 * A compilation unit start with an optional package declaration,
 * followed by zero or more import declarations,
 * followed by zero or more type declarations.
 *
 * @author Julio Vilmar Gesser
 * @see PackageDeclaration
 * @see ImportDeclaration
 * @see TypeDeclaration
 * @see Storage
 */
public class CompilationUnit extends Node {

    @OptionalProperty
    private PackageDeclaration packageDeclaration;

    private NodeList<ImportDeclaration> imports;

    private NodeList<TypeDeclaration<?>> types;

    @OptionalProperty
    private ModuleDeclaration module;

    @InternalProperty
    private Storage storage;

    public CompilationUnit() {
        this(null, null, new NodeList<>(), new NodeList<>(), null);
    }

    public CompilationUnit(String packageDeclaration) {
        this(null, new PackageDeclaration(new Name(packageDeclaration)), new NodeList<>(), new NodeList<>(), null);
    }

    @AllFieldsConstructor
    public CompilationUnit(PackageDeclaration packageDeclaration, NodeList<ImportDeclaration> imports, NodeList<TypeDeclaration<?>> types, ModuleDeclaration module) {
        this(null, packageDeclaration, imports, types, module);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public CompilationUnit(TokenRange tokenRange, PackageDeclaration packageDeclaration, NodeList<ImportDeclaration> imports, NodeList<TypeDeclaration<?>> types, ModuleDeclaration module) {
        super(tokenRange);
        setPackageDeclaration(packageDeclaration);
        setImports(imports);
        setTypes(types);
        setModule(module);
        customInitialization();
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.AcceptGenerator")
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.AcceptGenerator")
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    /**
     * Return a list containing all comments declared in this compilation unit.
     * Including javadocs, line comments and block comments of all types,
     * inner-classes and other members.<br>
     * If there is no comment, an empty list is returned.
     *
     * @return list with all comments of this compilation unit.
     * @see JavadocComment
     * @see com.github.javaparser.ast.comments.LineComment
     * @see com.github.javaparser.ast.comments.BlockComment
     */
    public List<Comment> getComments() {
        return this.getAllContainedComments();
    }

    /**
     * Retrieves the list of imports declared in this compilation unit or
     * <code>null</code> if there is no import.
     *
     * @return the list of imports or <code>none</code> if there is no import
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<ImportDeclaration> getImports() {
        return imports;
    }

    public ImportDeclaration getImport(int i) {
        return getImports().get(i);
    }

    /**
     * Retrieves the package declaration of this compilation unit.<br>
     * If this compilation unit has no package declaration (default package),
     * <code>Optional.none()</code> is returned.
     *
     * @return the package declaration or <code>none</code>
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<PackageDeclaration> getPackageDeclaration() {
        return Optional.ofNullable(packageDeclaration);
    }

    /**
     * Return the list of top level types declared in this compilation unit.<br>
     * If there are no types declared, <code>none</code> is returned.
     *
     * @return the list of types or <code>none</code> null if there is no type
     * @see AnnotationDeclaration
     * @see ClassOrInterfaceDeclaration
     * @see EnumDeclaration
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<TypeDeclaration<?>> getTypes() {
        return types;
    }

    /**
     * Convenience method that wraps <code>getTypes()</code>.<br>
     * If <code>i</code> is out of bounds, throws <code>IndexOutOfBoundsException.</code>
     *
     * @param i the index of the type declaration to retrieve
     */
    public TypeDeclaration<?> getType(int i) {
        return getTypes().get(i);
    }

    /**
     * Sets the list of imports of this compilation unit. The list is initially
     * <code>null</code>.
     *
     * @param imports the list of imports
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public CompilationUnit setImports(final NodeList<ImportDeclaration> imports) {
        assertNotNull(imports);
        if (imports == this.imports) {
            return (CompilationUnit) this;
        }
        notifyPropertyChange(ObservableProperty.IMPORTS, this.imports, imports);
        if (this.imports != null)
            this.imports.setParentNode(null);
        this.imports = imports;
        setAsParentNodeOf(imports);
        return this;
    }

    public CompilationUnit setImport(int i, ImportDeclaration imports) {
        getImports().set(i, imports);
        return this;
    }

    public CompilationUnit addImport(ImportDeclaration importDeclaration) {
        if (getImports().stream().noneMatch(im -> im.toString().equals(importDeclaration.toString()))) {
            getImports().add(importDeclaration);
        }
        return this;
    }

    /**
     * Sets or clear the package declarations of this compilation unit.
     *
     * @param packageDeclaration the packageDeclaration declaration to set or <code>null</code> to default package
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public CompilationUnit setPackageDeclaration(final PackageDeclaration packageDeclaration) {
        if (packageDeclaration == this.packageDeclaration) {
            return (CompilationUnit) this;
        }
        notifyPropertyChange(ObservableProperty.PACKAGE_DECLARATION, this.packageDeclaration, packageDeclaration);
        if (this.packageDeclaration != null)
            this.packageDeclaration.setParentNode(null);
        this.packageDeclaration = packageDeclaration;
        setAsParentNodeOf(packageDeclaration);
        return this;
    }

    /**
     * Sets the list of types declared in this compilation unit.
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public CompilationUnit setTypes(final NodeList<TypeDeclaration<?>> types) {
        assertNotNull(types);
        if (types == this.types) {
            return (CompilationUnit) this;
        }
        notifyPropertyChange(ObservableProperty.TYPES, this.types, types);
        if (this.types != null)
            this.types.setParentNode(null);
        this.types = types;
        setAsParentNodeOf(types);
        return this;
    }

    public CompilationUnit setType(int i, TypeDeclaration<?> type) {
        NodeList<TypeDeclaration<?>> copy = new NodeList<>();
        copy.addAll(getTypes());
        getTypes().set(i, type);
        notifyPropertyChange(ObservableProperty.TYPES, copy, types);
        return this;
    }

    public CompilationUnit addType(TypeDeclaration<?> type) {
        NodeList<TypeDeclaration<?>> copy = new NodeList<>();
        copy.addAll(getTypes());
        getTypes().add(type);
        notifyPropertyChange(ObservableProperty.TYPES, copy, types);
        return this;
    }

    /**
     * sets the package declaration of this compilation unit
     *
     * @param name the name of the package
     * @return this, the {@link CompilationUnit}
     */
    public CompilationUnit setPackageDeclaration(String name) {
        setPackageDeclaration(new PackageDeclaration(parseName(name)));
        return this;
    }

    /**
     * Add an import to the list of {@link ImportDeclaration} of this compilation unit<br>
     * shorthand for {@link #addImport(String, boolean, boolean)} with name,false,false
     *
     * @param name the import name
     * @return this, the {@link CompilationUnit}
     */
    public CompilationUnit addImport(String name) {
        return addImport(name, false, false);
    }

    /**
     * Add an import to the list of {@link ImportDeclaration} of this compilation unit<br>
     * shorthand for {@link #addImport(String)} with clazz.getName()
     *
     * @param clazz the class to import
     * @return this, the {@link CompilationUnit}
     * @throws RuntimeException if clazz is an anonymous or local class
     */
    public CompilationUnit addImport(Class<?> clazz) {
        if (clazz.isArray()) {
            return addImport(clazz.getComponentType());
        }
        if (ClassUtils.isPrimitiveOrWrapper(clazz) || "java.lang".equals(clazz.getPackage().getName()))
            return this;
        else if (clazz.isMemberClass())
            return addImport(clazz.getName().replace("$", "."));
        else if (clazz.isAnonymousClass() || clazz.isLocalClass())
            throw new RuntimeException(clazz.getName() + " is an anonymous or local class therefore it can't be added with addImport");
        return addImport(clazz.getName());
    }

    /**
     * Add an import to the list of {@link ImportDeclaration} of this compilation unit<br>
     * <b>This method check if no import with the same name is already in the list</b>
     *
     * @param name the import name
     * @param isStatic is it an "import static"
     * @param isAsterisk does the import end with ".*"
     * @return this, the {@link CompilationUnit}
     */
    public CompilationUnit addImport(String name, boolean isStatic, boolean isAsterisk) {
        final StringBuilder i = new StringBuilder("import ");
        if (isStatic) {
            i.append("static ");
        }
        i.append(name);
        if (isAsterisk) {
            i.append(".*");
        }
        i.append(";");
        return addImport(parseImport(i.toString()));
    }

    /**
     * Add a public class to the types of this compilation unit
     *
     * @param name the class name
     * @return the newly created class
     */
    public ClassOrInterfaceDeclaration addClass(String name) {
        return addClass(name, Modifier.Keyword.PUBLIC);
    }

    /**
     * Add a class to the types of this compilation unit
     *
     * @param name the class name
     * @param modifiers the modifiers (like Modifier.PUBLIC)
     * @return the newly created class
     */
    public ClassOrInterfaceDeclaration addClass(String name, Modifier.Keyword... modifiers) {
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = new ClassOrInterfaceDeclaration(createModifierList(modifiers), false, name);
        getTypes().add(classOrInterfaceDeclaration);
        return classOrInterfaceDeclaration;
    }

    /**
     * Add a public interface class to the types of this compilation unit
     *
     * @param name the interface name
     * @return the newly created class
     */
    public ClassOrInterfaceDeclaration addInterface(String name) {
        return addInterface(name, Modifier.Keyword.PUBLIC);
    }

    /**
     * Add an interface to the types of this compilation unit
     *
     * @param name the interface name
     * @param modifiers the modifiers (like Modifier.PUBLIC)
     * @return the newly created class
     */
    public ClassOrInterfaceDeclaration addInterface(String name, Modifier.Keyword... modifiers) {
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = new ClassOrInterfaceDeclaration(createModifierList(modifiers), true, name);
        getTypes().add(classOrInterfaceDeclaration);
        return classOrInterfaceDeclaration;
    }

    /**
     * Add a public enum to the types of this compilation unit
     *
     * @param name the enum name
     * @return the newly created class
     */
    public EnumDeclaration addEnum(String name) {
        return addEnum(name, Modifier.Keyword.PUBLIC);
    }

    /**
     * Add an enum to the types of this compilation unit
     *
     * @param name the enum name
     * @param modifiers the modifiers (like Modifier.PUBLIC)
     * @return the newly created class
     */
    public EnumDeclaration addEnum(String name, Modifier.Keyword... modifiers) {
        EnumDeclaration enumDeclaration = new EnumDeclaration(createModifierList(modifiers), name);
        getTypes().add(enumDeclaration);
        return enumDeclaration;
    }

    /**
     * Add a public annotation declaration to the types of this compilation unit
     *
     * @param name the annotation name
     * @return the newly created class
     */
    public AnnotationDeclaration addAnnotationDeclaration(String name) {
        return addAnnotationDeclaration(name, Modifier.Keyword.PUBLIC);
    }

    /**
     * Add an annotation declaration to the types of this compilation unit
     *
     * @param name the annotation name
     * @param modifiers the modifiers (like Modifier.PUBLIC)
     * @return the newly created class
     */
    public AnnotationDeclaration addAnnotationDeclaration(String name, Modifier.Keyword... modifiers) {
        AnnotationDeclaration annotationDeclaration = new AnnotationDeclaration(createModifierList(modifiers), name);
        getTypes().add(annotationDeclaration);
        return annotationDeclaration;
    }

    /**
     * Try to get a top level class declaration by its name
     *
     * @param className the class name (case-sensitive)
     */
    public Optional<ClassOrInterfaceDeclaration> getClassByName(String className) {
        return getTypes().stream().filter(type -> type.getNameAsString().equals(className) && type instanceof ClassOrInterfaceDeclaration && !((ClassOrInterfaceDeclaration) type).isInterface()).findFirst().map(t -> (ClassOrInterfaceDeclaration) t);
    }

    /**
     * Try to get a top level interface declaration by its name
     *
     * @param interfaceName the interface name (case-sensitive)
     */
    public Optional<ClassOrInterfaceDeclaration> getInterfaceByName(String interfaceName) {
        return getTypes().stream().filter(type -> type.getNameAsString().equals(interfaceName) && type instanceof ClassOrInterfaceDeclaration && ((ClassOrInterfaceDeclaration) type).isInterface()).findFirst().map(t -> (ClassOrInterfaceDeclaration) t);
    }

    /**
     * Try to get a top level enum declaration by its name
     *
     * @param enumName the enum name (case-sensitive)
     */
    public Optional<EnumDeclaration> getEnumByName(String enumName) {
        return getTypes().stream().filter(type -> type.getNameAsString().equals(enumName) && type instanceof EnumDeclaration).findFirst().map(t -> (EnumDeclaration) t);
    }

    /**
     * @return the name that the primary type in this file should have, according to the filename in {@link Storage#getFileName()}.
     * Empty if no file information is present (when this compilation unit wasn't parsed from a file.)
     */
    public Optional<String> getPrimaryTypeName() {
        return getStorage().map(Storage::getFileName).map(Utils::removeFileExtension);
    }

    /**
     * @return the type whose name corresponds to the file name.
     * Empty if no file information is present (when this compilation unit wasn't parsed from a file.)
     * If for some strange reason there are multiple types of this name, the first one is returned.
     */
    public Optional<TypeDeclaration<?>> getPrimaryType() {
        return getPrimaryTypeName().flatMap(name -> getTypes().stream().filter(t -> t.getNameAsString().equals(name)).findFirst());
    }

    /**
     * Try to get a top level annotation type declaration by its name
     *
     * @param annotationName the annotation name (case-sensitive)
     */
    public Optional<AnnotationDeclaration> getAnnotationDeclarationByName(String annotationName) {
        return getTypes().stream().filter(type -> type.getNameAsString().equals(annotationName) && type instanceof AnnotationDeclaration).findFirst().map(t -> (AnnotationDeclaration) t);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < imports.size(); i++) {
            if (imports.get(i) == node) {
                imports.remove(i);
                return true;
            }
        }
        if (module != null) {
            if (node == module) {
                removeModule();
                return true;
            }
        }
        if (packageDeclaration != null) {
            if (node == packageDeclaration) {
                removePackageDeclaration();
                return true;
            }
        }
        for (int i = 0; i < types.size(); i++) {
            if (types.get(i) == node) {
                types.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public CompilationUnit removePackageDeclaration() {
        return setPackageDeclaration((PackageDeclaration) null);
    }

    /**
     * @return the module declared in this compilation unit.
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<ModuleDeclaration> getModule() {
        return Optional.ofNullable(module);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public CompilationUnit setModule(final ModuleDeclaration module) {
        if (module == this.module) {
            return (CompilationUnit) this;
        }
        notifyPropertyChange(ObservableProperty.MODULE, this.module, module);
        if (this.module != null)
            this.module.setParentNode(null);
        this.module = module;
        setAsParentNodeOf(module);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public CompilationUnit removeModule() {
        return setModule((ModuleDeclaration) null);
    }

    /**
     * @return information about where this compilation unit was loaded from, or empty if it wasn't loaded from a file.
     */
    public Optional<Storage> getStorage() {
        return Optional.ofNullable(storage);
    }

    public CompilationUnit setStorage(Path path) {
        this.storage = new Storage(this, path);
        return this;
    }

    public CompilationUnit setStorage(Path path, Charset charset) {
        this.storage = new Storage(this, path, charset);
        return this;
    }

    /**
     * Create (or overwrite) a module declaration in this compilation unit with name "name".
     *
     * @return the module
     */
    public ModuleDeclaration setModule(String name) {
        final ModuleDeclaration module = new ModuleDeclaration(parseName(name), false);
        setModule(module);
        return module;
    }

    /**
     * Recalculates the ranges of all nodes by looking at the sizes of the tokens.
     * This is useful when you have manually inserted or deleted tokens and still want to use the ranges.
     */
    public void recalculatePositions() {
        if (!getTokenRange().isPresent()) {
            throw new IllegalStateException("Can't recalculate positions without tokens.");
        }
        Position cursor = Position.HOME;
        for (JavaToken t : getTokenRange().get()) {
            int tokenLength = t.getKind() == EOF.getKind() ? 0 : t.getText().length() - 1;
            t.setRange(range(cursor, cursor.right(tokenLength)));
            if (t.getCategory().isEndOfLine()) {
                cursor = cursor.nextLine();
            } else {
                cursor = cursor.right(tokenLength + 1);
            }
        }
    }

    /**
     * Information about where this compilation unit was loaded from.
     * This class only stores the absolute location.
     * For more flexibility use SourceRoot.
     */
    public static class Storage {

        private final CompilationUnit compilationUnit;

        private final Path path;

        private final Charset encoding;

        private Storage(CompilationUnit compilationUnit, Path path) {
            this.compilationUnit = compilationUnit;
            this.path = path.toAbsolutePath();
            this.encoding = UTF8;
        }

        private Storage(CompilationUnit compilationUnit, Path path, Charset encoding) {
            this.compilationUnit = compilationUnit;
            this.path = path.toAbsolutePath();
            this.encoding = encoding;
        }

        /**
         * @return the path to the source for this CompilationUnit
         */
        public Path getPath() {
            return path;
        }

        /**
         * @return the CompilationUnit this Storage is about.
         */
        public CompilationUnit getCompilationUnit() {
            return compilationUnit;
        }

        /**
         * @return the encoding used to read the file.
         */
        public Charset getEncoding() {
            return encoding;
        }

        /**
         * @return the source root directory, calculated from the path of this compiation unit, and the package
         * declaration of this compilation unit. If the package declaration is invalid (when it does not match the end
         * of the path) a RuntimeException is thrown.
         */
        public Path getSourceRoot() {
            final Optional<String> pkgAsString = compilationUnit.getPackageDeclaration().map(NodeWithName::getNameAsString);
            return pkgAsString.map(p -> Paths.get(CodeGenerationUtils.packageToPath(p))).map(pkg -> subtractPaths(getDirectory(), pkg)).orElse(getDirectory());
        }

        public String getFileName() {
            return path.getFileName().toString();
        }

        public Path getDirectory() {
            return path.getParent();
        }

        /**
         * Saves the compilation unit to its original location
         */
        public void save() {
            save(cu -> new PrettyPrinter().print(cu));
        }

        /**
         * Saves a compilation unit to its original location with formatting according to the function passed as a
         * parameter.
         *
         * @param makeOutput a function that formats the compilation unit
         */
        public void save(Function<CompilationUnit, String> makeOutput) {
            save(makeOutput, encoding);
        }

        /**
         * Saves a compilation unit to its original location with formatting and encoding according to the function and
         * encoding passed as a parameter.
         *
         * @param makeOutput a function that formats the compilation unit
         * @param encoding the encoding to use for the saved file
         */
        public void save(Function<CompilationUnit, String> makeOutput, Charset encoding) {
            try {
                Files.createDirectories(path.getParent());
                final String code = makeOutput.apply(getCompilationUnit());
                Files.write(path, code.getBytes(encoding));
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        }

        public ParseResult<CompilationUnit> reparse(JavaParser javaParser) {
            try {
                return javaParser.parse(ParseStart.COMPILATION_UNIT, provider(getPath()));
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        }
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public CompilationUnit clone() {
        return (CompilationUnit) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public CompilationUnitMetaModel getMetaModel() {
        return JavaParserMetaModel.compilationUnitMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        for (int i = 0; i < imports.size(); i++) {
            if (imports.get(i) == node) {
                imports.set(i, (ImportDeclaration) replacementNode);
                return true;
            }
        }
        if (module != null) {
            if (node == module) {
                setModule((ModuleDeclaration) replacementNode);
                return true;
            }
        }
        if (packageDeclaration != null) {
            if (node == packageDeclaration) {
                setPackageDeclaration((PackageDeclaration) replacementNode);
                return true;
            }
        }
        for (int i = 0; i < types.size(); i++) {
            if (types.get(i) == node) {
                types.set(i, (TypeDeclaration) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }
}
