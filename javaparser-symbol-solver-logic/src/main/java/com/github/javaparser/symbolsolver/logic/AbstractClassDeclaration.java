/*
 * Copyright 2016 Federico Tomassetti
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.github.javaparser.symbolsolver.logic;

import com.github.javaparser.resolution.declarations.ResolvedClassDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;

import java.util.ArrayList;
import java.util.List;

/**
 * A common ancestor for all ClassDeclarations.
 *
 * @author Federico Tomassetti
 */
public abstract class AbstractClassDeclaration extends AbstractTypeDeclaration implements ResolvedClassDeclaration {

    ///
    /// Public
    ///

    @Override
    public boolean hasName() {
        return getQualifiedName() != null;
    }

    @Override
    public final List<ResolvedReferenceType> getAllSuperClasses() {
        List<ResolvedReferenceType> superclasses = new ArrayList<>();
        ResolvedReferenceType superClass = getSuperClass();
        if (superClass != null) {
            superclasses.add(superClass);
            superclasses.addAll(superClass.getAllClassesAncestors());
        }

        if (superclasses.removeIf(s -> s.getQualifiedName().equals(Object.class.getCanonicalName()))) {
            superclasses.add(object());
        }
        return superclasses;
    }

    @Override
    public final List<ResolvedReferenceType> getAllInterfaces() {
        List<ResolvedReferenceType> interfaces = new ArrayList<>();
        for (ResolvedReferenceType interfaceDeclaration : getInterfaces()) {
            interfaces.add(interfaceDeclaration);
            interfaces.addAll(interfaceDeclaration.getAllInterfacesAncestors());
        }
        ResolvedReferenceType superClass = this.getSuperClass();
        if (superClass != null) {
            interfaces.addAll(superClass.getAllInterfacesAncestors());
        }
        return interfaces;
    }

    @Override
    public final ResolvedClassDeclaration asClass() {
        return this;
    }

    ///
    /// Protected
    ///

    /**
     * An implementation of the Object class.
     */
    protected abstract ResolvedReferenceType object();

}
