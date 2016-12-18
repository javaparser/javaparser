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
import com.github.javaparser.ast.imports.ImportDeclaration;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.utils.ClassUtils;

import java.util.Arrays;
import java.util.EnumSet;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * <p>
 * This class represents the entire compilation unit. Each java file denotes a
 * compilation unit.
 * </p>
 * The CompilationUnit is constructed following the syntax:<br>
 * <p>
 * <pre>
 * {@code
 * CompilationUnit ::=  ( }{@link PackageDeclaration}{@code )?
 *                      ( }{@link ImportDeclaration}{@code )*
 *                      ( }{@link TypeDeclaration}{@code )*
 * }
 * </pre>
 *
 * @author Julio Vilmar Gesser
 */
public final class CompilationUnit extends Node {

    private PackageDeclaration packageDeclaration;

    private NodeList<ImportDeclaration> imports;

    private NodeList<TypeDeclaration<?>> types;

    public CompilationUnit() {
        this(null, null, new NodeList<>(), new NodeList<>());
    }

    public CompilationUnit(String packageDeclaration) {
        this(null, new PackageDeclaration(new Name(packageDeclaration)), new NodeList<>(), new NodeList<>());
    }

    public CompilationUnit(PackageDeclaration packageDeclaration, NodeList<ImportDeclaration> imports, NodeList<TypeDeclaration<?>> types) {
        this(null, packageDeclaration, imports, types);
    }

    public CompilationUnit(Range range, PackageDeclaration packageDeclaration, NodeList<ImportDeclaration> imports,
                           NodeList<TypeDeclaration<?>> types) {
        super(range);
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
    public CompilationUnit setImports(NodeList<ImportDeclaration> imports) {
        notifyPropertyChange(ObservableProperty.IMPORTS, this.imports, imports);
        this.imports = assertNotNull(imports);
        setAsParentNodeOf(this.imports);
        return this;
    }

    /**
     * Sets or clear the package declarations of this compilation unit.
     *
     * @param pakage the packageDeclaration declaration to set or <code>null</code> to default package
     */
    public CompilationUnit setPackageDeclaration(PackageDeclaration pakage) {
        notifyPropertyChange(ObservableProperty.PACKAGE_DECLARATION, this.packageDeclaration, pakage);
        this.packageDeclaration = pakage;
        setAsParentNodeOf(this.packageDeclaration);
        return this;
    }

    /**
     * Sets the list of types declared in this compilation unit.
     *
     * @param types the lis of types
     */
    public CompilationUnit setTypes(NodeList<TypeDeclaration<?>> types) {
        notifyPropertyChange(ObservableProperty.TYPES, this.types, types);
        this.types = assertNotNull(types);
        setAsParentNodeOf(this.types);
        return this;
    }

    /**
     * sets the package declaration of this compilation unit
     *
     * @param name the name of the package
     * @return this, the {@link CompilationUnit}
     */
    public CompilationUnit setPackageDeclaration(String name) {
        setPackageDeclaration(new PackageDeclaration(Name.parse(name)));
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
        else if (clazz.isArray() && !ClassUtils.isPrimitiveOrWrapper(clazz.getComponentType())
                && !clazz.getComponentType().getName().startsWith("java.lang"))
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
            importDeclaration.setParentNode(this);
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
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = new ClassOrInterfaceDeclaration(
                Arrays.stream(modifiers)
                        .collect(Collectors.toCollection(() -> EnumSet.noneOf(Modifier.class))),
                false, name);
        getTypes().add(classOrInterfaceDeclaration);
        classOrInterfaceDeclaration.setParentNode(this);
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
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = new ClassOrInterfaceDeclaration(
                Arrays.stream(modifiers)
                        .collect(Collectors.toCollection(() -> EnumSet.noneOf(Modifier.class))),
                true, name);
        getTypes().add(classOrInterfaceDeclaration);
        classOrInterfaceDeclaration.setParentNode(this);
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
        EnumDeclaration enumDeclaration = new EnumDeclaration(Arrays.stream(modifiers)
                .collect(Collectors.toCollection(() -> EnumSet.noneOf(Modifier.class))), name);
        getTypes().add(enumDeclaration);
        enumDeclaration.setParentNode(this);
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
        AnnotationDeclaration annotationDeclaration = new AnnotationDeclaration(Arrays.stream(modifiers)
                .collect(Collectors.toCollection(() -> EnumSet.noneOf(Modifier.class))), name);
        getTypes().add(annotationDeclaration);
        annotationDeclaration.setParentNode(this);
        return annotationDeclaration;
    }

    /**
     * Try to get a class by its name
     *
     * @param className the class name (case-sensitive)
     * @return null if not found, the class otherwise
     */
    public ClassOrInterfaceDeclaration getClassByName(String className) {
        return (ClassOrInterfaceDeclaration) getTypes().stream().filter(type -> type.getNameAsString().equals(className)
                && type instanceof ClassOrInterfaceDeclaration && !((ClassOrInterfaceDeclaration) type).isInterface())
                .findFirst().orElse(null);
    }

    /**
     * Try to get an interface by its name
     *
     * @param interfaceName the interface name (case-sensitive)
     * @return null if not found, the interface otherwise
     */
    public ClassOrInterfaceDeclaration getInterfaceByName(String interfaceName) {
        return (ClassOrInterfaceDeclaration) getTypes().stream().filter(type -> type.getNameAsString().equals(interfaceName)
                && type instanceof ClassOrInterfaceDeclaration && ((ClassOrInterfaceDeclaration) type).isInterface())
                .findFirst().orElse(null);
    }

    /**
     * Try to get an enum by its name
     *
     * @param enumName the enum name (case-sensitive)
     * @return null if not found, the enum otherwise
     */
    public EnumDeclaration getEnumByName(String enumName) {
        return (EnumDeclaration) getTypes().stream().filter(type -> type.getNameAsString().equals(enumName)
                && type instanceof EnumDeclaration)
                .findFirst().orElse(null);
    }

    /**
     * Try to get an annotation by its name
     *
     * @param annotationName the annotation name (case-sensitive)
     * @return null if not found, the annotation otherwise
     */
    public AnnotationDeclaration getAnnotationDeclarationByName(String annotationName) {
        return (AnnotationDeclaration) getTypes().stream().filter(type -> type.getNameAsString().equals(annotationName)
                && type instanceof AnnotationDeclaration)
                .findFirst().orElse(null);
    }

    @Override
    public List<NodeList<?>> getNodeLists() {
        return Arrays.asList(imports, types);
    }
}
