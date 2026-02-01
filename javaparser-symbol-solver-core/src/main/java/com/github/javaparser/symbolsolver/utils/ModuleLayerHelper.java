/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2025 The JavaParser Team.
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
package com.github.javaparser.symbolsolver.utils;

import java.lang.reflect.InvocationTargetException;
import java.util.HashMap;
import java.util.Optional;
import java.util.Set;

public class ModuleLayerHelper {

    /**
     * The JDK doesn't expose a simple mechanism for listing modules containing classes loaded by a classloader,
     * so users who would like to solve types in modules need to provide a list of module layers containing the
     * modules that should be discoverable by the type solver.
     * <br>
     * To maintain compatibility with Java 8, the ModuleLayer and Module classes introduced in Java 9 cannot
     * be used, so reflection and the Object type are used instead.
     * <br>
     * Note: JavaParser currently does not support the exports...to... feature since necessary state information
     * to handle this correctly is not tracked. If such support is added in the future, the signature of this
     * method may change to include the extra information.
     *
     * @param moduleLayers a list of java.lang.ModuleLayer instances that should be used for type solving
     * @return a map of ModuleName->ExportedPackages
     */
    public static HashMap<String, Set<String>> getModulePackagesFromLayers(Iterable<Object> moduleLayers) {
        HashMap<String, Set<String>> modulePackages = new HashMap<>();

        for (Object moduleLayer : moduleLayers) {
            if (!moduleLayer.getClass().getCanonicalName().equals("java.lang.ModuleLayer")) {
                throw new IllegalArgumentException(
                        "getModuleExportedPackagesFromLayer must be called with a ModuleLayer argument but was called with "
                                + moduleLayer.getClass().getCanonicalName());
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
                Set<Object> modulesSet = (Set<Object>)
                        moduleLayer.getClass().getMethod("modules").invoke(moduleLayer);

                for (Object module : modulesSet) {
                    String name = module.getClass()
                            .getMethod("getName")
                            .invoke(module)
                            .toString();
                    Set<String> packages = (Set<String>)
                            module.getClass().getMethod("getPackages").invoke(module);

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

        return modulePackages;
    }

    /**
     * A ModuleLayer needs to be provided for the ReflectionTypeSolver and the boot layer (the module layer
     * containing the module `java.base`) is chosen as a default. There may be advanced cases where this assumption
     * is incorrect. In these cases, the ClassLoaderTypeSolver should be used instead.
     *
     * @return the boot module layer, if it exists (i.e. on Java > 9)
     */
    public static Optional<Object> getBootModuleLayer() {
        try {
            /* This code is equivalent to the snippet below, but is done with reflection to maintain compatibility with
             * Java 8
             *
             * ModuleLayer bootModuleLayer = ModuleLayer.boot();
             * moduleLayers.add(bootModuleLayer)
             */
            Class<?> moduleLayerClass = Class.forName("java.lang.ModuleLayer");
            Object bootModuleLayer = moduleLayerClass.getDeclaredMethod("boot").invoke(moduleLayerClass);
            return Optional.of(bootModuleLayer);
        } catch (ClassNotFoundException
                | NoSuchMethodException
                | IllegalAccessException
                | InvocationTargetException e) {
            // Expected for Java 8, so just return empty optional
            return Optional.empty();
        }
    }
}
