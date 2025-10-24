/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2024 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.resolution.typesolvers;

import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionFactory;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.*;

/**
 * This TypeSolver wraps a ClassLoader. It can solve all types that the given ClassLoader can load.
 * This is intended to be used with custom classloaders. To support typical cases based on reflection
 * just use the ReflectionTypeSolver
 *
 * @author Federico Tomassetti
 */
public class ClassLoaderTypeSolver implements TypeSolver {

    private TypeSolver parent;
    private ClassLoader classLoader;
    private HashMap<String, Set<String>> modulePackages;

    public ClassLoaderTypeSolver(ClassLoader classLoader) {
        this.classLoader = classLoader;
        this.modulePackages = new HashMap<>();
    }

    /**
     * Create a ClassLoaderTypeSolver with a list of module layers to check when solving types in modules. If
     * moduleLayers is empty, tryToSolveTypeInModule will always return SymbolReference.unsolved
     *
     * @param classLoader the ClassLoader that should be used for type solving
     * @param moduleLayers MUST be {@code Iterable<java.lang.ModuleLayer>}. Object is only used in the signature for
     *                     Java 8 compatibility.
     */
    public ClassLoaderTypeSolver(ClassLoader classLoader, Iterable<Object> moduleLayers) {
        this(classLoader);
        addModuleLayers(moduleLayers);
    }

    public void addModuleLayers(Iterable<Object> moduleLayers) {
        for (Object moduleLayer : moduleLayers) {
            if (!moduleLayer.getClass().getCanonicalName().equals("java.lang.ModuleLayer")) {
                continue;
            }
            try {
                /* This code is equivalent to the snippet below, but is done with reflection to maintain compatibility
                 * with Java 8
                 *
                 * Set<Module> modulesSet = moduleLayer.modules();
                 *
                 * for (Module module : modulesSet) {
                 *   String name = module.getName();
                 *   Set<String> packages = module.getPackages();
                 *
                 *   ...
                 * }
                 */
                Set<Object> modulesSet = (Set<Object>) moduleLayer.getClass().getMethod("modules").invoke(moduleLayer);

                for (Object module : modulesSet) {
                    String name = module.getClass().getMethod("getName").invoke(module).toString();
                    Set<String> packages = (Set<String>) module.getClass().getMethod("getPackages").invoke(module);

                    if (modulePackages.containsKey(name)) {
                        modulePackages.get(name).addAll(packages);
                    } else {
                        modulePackages.put(name, packages);
                    }
                }
            } catch (IllegalAccessException | InvocationTargetException | NoSuchMethodException e) {
                // Expected for Java 8, so do nothing
            }
        }
    }

    @Override
    public TypeSolver getParent() {
        return parent;
    }

    @Override
    public void setParent(TypeSolver parent) {
        Objects.requireNonNull(parent);
        if (this.parent != null) {
            throw new IllegalStateException("This TypeSolver already has a parent.");
        }
        if (parent == this) {
            throw new IllegalStateException("The parent of this TypeSolver cannot be itself.");
        }
        this.parent = parent;
    }

    protected boolean filterName(String name) {
        return true;
    }

    @Override
    public SymbolReference<ResolvedReferenceTypeDeclaration> tryToSolveTypeInModule(String qualifiedModuleName, String simpleTypeName) {
        if (filterName(qualifiedModuleName)) {
                if (classLoader == null) {
                    throw new RuntimeException(
                            "The ClassLoaderTypeSolver has been probably loaded through the bootstrap class loader. This usage is not supported by the JavaSymbolSolver");
                }
                if (modulePackages.containsKey(qualifiedModuleName)) {
                    Set<String> packages = modulePackages.get(qualifiedModuleName);

                    for (String packageName : packages) {
                        String className = packageName + "." + simpleTypeName;
                        SymbolReference<ResolvedReferenceTypeDeclaration> maybeSolved = tryToSolveType(className);
                        if (maybeSolved.isSolved()) {
                            return maybeSolved;
                        }
                    }
                }
                return SymbolReference.unsolved();
        }
        return SymbolReference.unsolved();
    }

    @Override
    public SymbolReference<ResolvedReferenceTypeDeclaration> tryToSolveType(String name) {
        if (filterName(name)) {
            try {
                // Some implementations could return null when the class was loaded through the bootstrap classloader
                // see https://docs.oracle.com/javase/8/docs/api/java/lang/Class.html#getClassLoader--
                if (classLoader == null) {
                    throw new RuntimeException(
                            "The ClassLoaderTypeSolver has been probably loaded through the bootstrap class loader. This usage is not supported by the JavaSymbolSolver");
                }

                Class<?> clazz = classLoader.loadClass(name);
                return SymbolReference.solved(ReflectionFactory.typeDeclarationFor(clazz, getRoot()));
            } catch (NoClassDefFoundError e) {
                // We can safely ignore this one because it is triggered when there are package names which are almost
                // the
                // same as class name, with the exclusion of the case.
                // For example:
                // java.lang.NoClassDefFoundError: com/github/javaparser/printer/ConcreteSyntaxModel
                // (wrong name: com/github/javaparser/printer/concretesyntaxmodel)
                // note that this exception seems to be thrown only on certain platform (mac yes, linux no)
                return SymbolReference.unsolved();
            } catch (ClassNotFoundException e) {
                // it could be an inner class
                int lastDot = name.lastIndexOf('.');
                if (lastDot == -1) {
                    return SymbolReference.unsolved();
                }
                String parentName = name.substring(0, lastDot);
                String childName = name.substring(lastDot + 1);
                SymbolReference<ResolvedReferenceTypeDeclaration> parent = tryToSolveType(parentName);
                if (parent.isSolved()) {
                    Optional<ResolvedReferenceTypeDeclaration> innerClass =
                            parent.getCorrespondingDeclaration().internalTypes().stream()
                                    .filter(it -> it.getName().equals(childName))
                                    .findFirst();
                    return innerClass.map(SymbolReference::solved).orElseGet(() -> SymbolReference.unsolved());
                }
                return SymbolReference.unsolved();
            }
        } else {
            return SymbolReference.unsolved();
        }
    }
}
