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

package com.github.javaparser.resolution.declarations;

import com.github.javaparser.resolution.types.ResolvedReferenceType;

import java.util.ArrayList;
import java.util.List;

/**
 * An interface declaration.
 *
 * @author Federico Tomassetti
 */
public interface ResolvedInterfaceDeclaration extends ResolvedReferenceTypeDeclaration,
        ResolvedTypeParametrizable, HasAccessSpecifier {

    @Override
    default boolean isInterface() {
        return true;
    }

    /**
     * Return the list of interfaces extended directly by this one.
     */
    List<ResolvedReferenceType> getInterfacesExtended();

    /**
     * Return the list of interfaces extended directly or indirectly by this one.
     */
    default List<ResolvedReferenceType> getAllInterfacesExtended() {
        List<ResolvedReferenceType> interfaces = new ArrayList<>();
        for (ResolvedReferenceType interfaceDeclaration : getInterfacesExtended()) {
            interfaces.add(interfaceDeclaration);
            interfaces.addAll(interfaceDeclaration.getAllInterfacesAncestors());
        }
        return interfaces;
    }
}
