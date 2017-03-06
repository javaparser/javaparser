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

import com.github.javaparser.JavaParser;
import com.github.javaparser.Range;
import com.github.javaparser.ast.body.AnnotationDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.modules.ModuleDeclaration;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.CompilationUnitMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.utils.ClassUtils;
import java.util.Arrays;
import java.util.EnumSet;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;
import static com.github.javaparser.JavaParser.parseName;
import static com.github.javaparser.utils.Utils.assertNotNull;

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
 */
public final class CompilationUnit extends Node {

    private PackageDeclaration packageDeclaration;

    private NodeList<ImportDeclaration> imports;

    private NodeList<TypeDeclaration<?>> types;

    private ModuleDeclaration module;

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

    public CompilationUnit(Range range, PackageDeclaration packageDeclaration, NodeList<ImportDeclaration> imports, NodeList<TypeDeclaration<?>> types, ModuleDeclaration module) {
        super(range);
        setModule(module);
        setPackageDeclaration(packageDeclaration);
        setImports(imports);
        setTypes(types);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
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
    public Optional<PackageDeclaration> getPackageDeclaration() {
        return Optional.ofNullable(packageDeclaration);
    }

    /**
     * Return the list of types declared in this compilation unit.<br>
     * If there is no types declared, <code>none</code> is returned.
     *
     * @return the list of types or <code>none</code> null if there is no type
     * @see AnnotationDeclaration
     * @see ClassOrInterfaceDeclaration
     * @see EnumDeclaration
     */
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
    public CompilationUnit setImports(final NodeList<ImportDeclaration> imports) {
        assertNotNull(imports);
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

    public CompilationUnit addImport(ImportDeclaration imports) {
        getImports().add(imports);
        return this;
    }

    /**
     * Sets or clear the package declarations of this compilation unit.
     *
     * @param packageDeclaration the packageDeclaration declaration to set or <code>null</code> to default package
     */
    public CompilationUnit setPackageDeclaration(final PackageDeclaration packageDeclaration) {
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
    public CompilationUnit setTypes(final NodeList<TypeDeclaration<?>> types) {
        assertNotNull(types);
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
     */
    public CompilationUnit addImport(Class<?> clazz) {
        if (ClassUtils.isPrimitiveOrWrapper(clazz) || clazz.getName().startsWith("java.lang"))
            return this;
        else if (clazz.isArray() && !ClassUtils.isPrimitiveOrWrapper(clazz.getComponentType()) && !clazz.getComponentType().getName().startsWith("java.lang"))
            return addImport(clazz.getComponentType().getName());
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
        ImportDeclaration importDeclaration = JavaParser.parseImport(i.toString());
        if (getImports().stream().anyMatch(im -> im.toString().equals(importDeclaration.toString())))
            return this;
        else {
            getImports().add(importDeclaration);
            return this;
        }
    }

    /**
     * Add a public class to the types of this compilation unit
     *
     * @param name the class name
     * @return the newly created class
     */
    public ClassOrInterfaceDeclaration addClass(String name) {
        return addClass(name, Modifier.PUBLIC);
    }

    /**
     * Add a class to the types of this compilation unit
     *
     * @param name the class name
     * @param modifiers the modifiers (like Modifier.PUBLIC)
     * @return the newly created class
     */
    public ClassOrInterfaceDeclaration addClass(String name, Modifier... modifiers) {
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = new ClassOrInterfaceDeclaration(Arrays.stream(modifiers).collect(Collectors.toCollection(() -> EnumSet.noneOf(Modifier.class))), false, name);
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
        return addInterface(name, Modifier.PUBLIC);
    }

    /**
     * Add an interface to the types of this compilation unit
     *
     * @param name the interface name
     * @param modifiers the modifiers (like Modifier.PUBLIC)
     * @return the newly created class
     */
    public ClassOrInterfaceDeclaration addInterface(String name, Modifier... modifiers) {
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = new ClassOrInterfaceDeclaration(Arrays.stream(modifiers).collect(Collectors.toCollection(() -> EnumSet.noneOf(Modifier.class))), true, name);
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
        return addEnum(name, Modifier.PUBLIC);
    }

    /**
     * Add an enum to the types of this compilation unit
     *
     * @param name the enum name
     * @param modifiers the modifiers (like Modifier.PUBLIC)
     * @return the newly created class
     */
    public EnumDeclaration addEnum(String name, Modifier... modifiers) {
        EnumDeclaration enumDeclaration = new EnumDeclaration(Arrays.stream(modifiers).collect(Collectors.toCollection(() -> EnumSet.noneOf(Modifier.class))), name);
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
        return addAnnotationDeclaration(name, Modifier.PUBLIC);
    }

    /**
     * Add an annotation declaration to the types of this compilation unit
     *
     * @param name the annotation name
     * @param modifiers the modifiers (like Modifier.PUBLIC)
     * @return the newly created class
     */
    public AnnotationDeclaration addAnnotationDeclaration(String name, Modifier... modifiers) {
        AnnotationDeclaration annotationDeclaration = new AnnotationDeclaration(Arrays.stream(modifiers).collect(Collectors.toCollection(() -> EnumSet.noneOf(Modifier.class))), name);
        getTypes().add(annotationDeclaration);
        return annotationDeclaration;
    }

    /**
     * Try to get a class by its name
     *
     * @param className the class name (case-sensitive)
     */
    public Optional<ClassOrInterfaceDeclaration> getClassByName(String className) {
        return getTypes().stream().filter(type -> type.getNameAsString().equals(className) && type instanceof ClassOrInterfaceDeclaration && !((ClassOrInterfaceDeclaration) type).isInterface()).findFirst().map(t -> (ClassOrInterfaceDeclaration) t);
    }

    /**
     * Try to get an interface by its name
     *
     * @param interfaceName the interface name (case-sensitive)
     */
    public Optional<ClassOrInterfaceDeclaration> getInterfaceByName(String interfaceName) {
        return getTypes().stream().filter(type -> type.getNameAsString().equals(interfaceName) && type instanceof ClassOrInterfaceDeclaration && ((ClassOrInterfaceDeclaration) type).isInterface()).findFirst().map(t -> (ClassOrInterfaceDeclaration) t);
    }

    /**
     * Try to get an enum by its name
     *
     * @param enumName the enum name (case-sensitive)
     */
    public Optional<EnumDeclaration> getEnumByName(String enumName) {
        return getTypes().stream().filter(type -> type.getNameAsString().equals(enumName) && type instanceof EnumDeclaration).findFirst().map(t -> (EnumDeclaration) t);
    }

    /**
     * Try to get an annotation by its name
     *
     * @param annotationName the annotation name (case-sensitive)
     */
    public Optional<AnnotationDeclaration> getAnnotationDeclarationByName(String annotationName) {
        return getTypes().stream().filter(type -> type.getNameAsString().equals(annotationName) && type instanceof AnnotationDeclaration).findFirst().map(t -> (AnnotationDeclaration) t);
    }

    @Override
    public List<NodeList<?>> getNodeLists() {
        return Arrays.asList(getImports(), getTypes());
    }

    @Override
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

    public CompilationUnit removePackageDeclaration() {
        return setPackageDeclaration((PackageDeclaration) null);
    }

    public Optional<ModuleDeclaration> getModule() {
        return Optional.ofNullable(module);
    }

    public CompilationUnit setModule(final ModuleDeclaration module) {
        notifyPropertyChange(ObservableProperty.MODULE, this.module, module);
        if (this.module != null)
            this.module.setParentNode(null);
        this.module = module;
        setAsParentNodeOf(module);
        return this;
    }

    public CompilationUnit removeModule() {
        return setModule((ModuleDeclaration) null);
    }

    @Override
    public CompilationUnit clone() {
        return (CompilationUnit) accept(new CloneVisitor(), null);
    }

    @Override
    public CompilationUnitMetaModel getMetaModel() {
        return JavaParserMetaModel.compilationUnitMetaModel;
    }
}

