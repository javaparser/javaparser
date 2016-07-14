/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2015 The JavaParser Team.
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

import static com.github.javaparser.Position.pos;
import static com.github.javaparser.ast.internal.Utils.ensureNotNull;

import java.util.List;

import com.github.javaparser.ASTHelper;
import com.github.javaparser.Range;
import com.github.javaparser.ast.body.AnnotationDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.EmptyTypeDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.ModifierSet;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * <p>
 * This class represents the entire compilation unit. Each java file denotes a
 * compilation unit.
 * </p>
 * The CompilationUnit is constructed following the syntax:<br>
 * 
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

    private PackageDeclaration pakage;

    private List<ImportDeclaration> imports;

    private List<TypeDeclaration> types;

    public CompilationUnit() {
    }

    public CompilationUnit(PackageDeclaration pakage, List<ImportDeclaration> imports, List<TypeDeclaration> types) {
        setPackage(pakage);
        setImports(imports);
        setTypes(types);
    }

    /**
     * @deprecated prefer using Range objects.
     */
    @Deprecated
    public CompilationUnit(int beginLine, int beginColumn, int endLine, int endColumn, PackageDeclaration pakage,
                           List<ImportDeclaration> imports, List<TypeDeclaration> types) {
        this(new Range(pos(beginLine, beginColumn), pos(endLine, endColumn)), pakage, imports, types);
    }

    public CompilationUnit(Range range, PackageDeclaration pakage, List<ImportDeclaration> imports,
                           List<TypeDeclaration> types) {
        super(range);
        setPackage(pakage);
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
     * If there is no comment, <code>null</code> is returned.
     * 
     * @return list with all comments of this compilation unit or
     *         <code>null</code>
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
     * @return the list of imports or <code>null</code> if there is no import
     */
    public List<ImportDeclaration> getImports() {
        imports = ensureNotNull(imports);
        return imports;
    }

    /**
     * Retrieves the package declaration of this compilation unit.<br>
     * If this compilation unit has no package declaration (default package),
     * <code>null</code> is returned.
     * 
     * @return the package declaration or <code>null</code>
     */
    public PackageDeclaration getPackage() {
        return pakage;
    }

    /**
     * Return the list of types declared in this compilation unit.<br>
     * If there is no types declared, <code>null</code> is returned.
     * 
     * @return the list of types or <code>null</code> null if there is no type
     * @see AnnotationDeclaration
     * @see ClassOrInterfaceDeclaration
     * @see EmptyTypeDeclaration
     * @see EnumDeclaration
     */
    public List<TypeDeclaration> getTypes() {
        types = ensureNotNull(types);
        return types;
    }

    /**
     * Sets the list of comments of this compilation unit.
     * 
     * @param comments
     *            the list of comments
     */
    public void setComments(List<Comment> comments) {
        throw new RuntimeException("Not implemented!");
    }

    /**
     * Sets the list of imports of this compilation unit. The list is initially
     * <code>null</code>.
     * 
     * @param imports
     *            the list of imports
     */
    public void setImports(List<ImportDeclaration> imports) {
        this.imports = imports;
        setAsParentNodeOf(this.imports);
    }

    /**
     * Sets or clear the package declarations of this compilation unit.
     * 
     * @param pakage
     *            the pakage declaration to set or <code>null</code> to default
     *            package
     */
    public void setPackage(PackageDeclaration pakage) {
        this.pakage = pakage;
        setAsParentNodeOf(this.pakage);
    }

    /**
     * Sets the list of types declared in this compilation unit.
     * 
     * @param types
     *            the lis of types
     */
    public void setTypes(List<TypeDeclaration> types) {
        this.types = types;
        setAsParentNodeOf(this.types);
    }

    /**
     * sets the package declaration of this compilation unit
     * 
     * @param name the name of the package
     * @return this, the {@link CompilationUnit}
     */
    public CompilationUnit setPackageName(String name) {
        setPackage(new PackageDeclaration(ASTHelper.createNameExpr(name)));
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
        return addImport(clazz.getName());
    }

    /**
     * Add an import to the list of {@link ImportDeclaration} of this compilation unit<br>
     * shorthand for {@link #addImport(String, boolean, boolean)} with name,false,false<br>
     * <b>This method check if no import with the same name is already in the list</b>
     * 
     * @param clazz the class to import
     * @return this, the {@link CompilationUnit}
     */
    public CompilationUnit addImportWithoutDuplicates(Class<?> clazz) {
        return addImportWithoutDuplicates(clazz.getName());
    }

    /**
     * Add an import to the list of {@link ImportDeclaration} of this compilation unit<br>
     * shorthand for {@link #addImport(String, boolean, boolean)} with name,false,false<br>
     * <b>This method check if no import with the same name is already in the list</b>
     * 
     * @param name the import name
     * @return this, the {@link CompilationUnit}
     */
    public CompilationUnit addImportWithoutDuplicates(final String name) {
        if (getImports().stream().anyMatch(i -> i.getName().getName().equals(name)))
            return this;
        else
            return addImport(name, false, false);
    }

    /**
     * Add an import to the list of {@link ImportDeclaration} of this compilation unit
     * 
     * @param name the import name
     * @param isStatic
     * @param isAsterisk
     * @return this, the {@link CompilationUnit}
     */
    public CompilationUnit addImport(String name, boolean isStatic, boolean isAsterisk) {
        ImportDeclaration importDeclaration = new ImportDeclaration(ASTHelper.createNameExpr(name), isStatic,
                isAsterisk);
        getImports().add(importDeclaration);
        importDeclaration.setParentNode(this);
        return this;
    }

    /**
     * Add a public class to the types of this compilation unit
     * 
     * @param name the class name
     * @return the newly created class
     */
    public ClassOrInterfaceDeclaration addClass(String name) {
        return addClass(name, ModifierSet.PUBLIC);
    }

    /**
     * Add a class to the types of this compilation unit
     * 
     * @param name the class name
     * @param modifiers the modifiers (like ModifierSet.PUBLIC)
     * @return the newly created class
     */
    public ClassOrInterfaceDeclaration addClass(String name, int modifiers) {
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = new ClassOrInterfaceDeclaration(modifiers,
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
        return addInterface(name, ModifierSet.PUBLIC);
    }

    /**
     * Add an interface to the types of this compilation unit
     * 
     * @param name the interface name
     * @param modifiers the modifiers (like ModifierSet.PUBLIC)
     * @return the newly created class
     */
    public ClassOrInterfaceDeclaration addInterface(String name, int modifiers) {
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = new ClassOrInterfaceDeclaration(modifiers,
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
        return addEnum(name, ModifierSet.PUBLIC);
    }

    /**
     * Add an enum to the types of this compilation unit
     * 
     * @param name the enum name
     * @param modifiers the modifiers (like ModifierSet.PUBLIC)
     * @return the newly created class
     */
    public EnumDeclaration addEnum(String name, int modifiers) {
        EnumDeclaration enumDeclaration = new EnumDeclaration(modifiers, name);
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
        return addAnnotationDeclaration(name, ModifierSet.PUBLIC);
    }

    /**
     * Add an annotation declaration to the types of this compilation unit
     * 
     * @param name the annotation name
     * @param modifiers the modifiers (like ModifierSet.PUBLIC)
     * @return the newly created class
     */
    public AnnotationDeclaration addAnnotationDeclaration(String name, int modifiers) {
        AnnotationDeclaration annotationDeclaration = new AnnotationDeclaration(modifiers, name);
        getTypes().add(annotationDeclaration);
        annotationDeclaration.setParentNode(this);
        return annotationDeclaration;
    }
}
