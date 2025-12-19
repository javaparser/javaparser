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

import com.github.javaparser.utils.Pair;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import javassist.CtClass;
import javassist.bytecode.ClassFile;
import javassist.bytecode.ConstPool;

public class JavassistModuleHelper {
    public static String MODULE_INFO_CLASS_NAME = "module-info";

    /**
     * Javassist does not provide support for modules beyond letting users fetch the module
     * attribute byte array, so the attribute needs to be parsed manually. This is done
     * according to <a href="https://docs.oracle.com/javase/specs/jvms/se25/html/jvms-4.html#jvms-4.7.25">The JVM Spec</a>
     * for the module attribute.
     *
     * @param moduleInfo the CtClass for module-info.class
     * @return a pair of [ModuleName, ExportedPackageNames] if the module attribute is not empty.
     */
    public static Optional<Pair<String, List<String>>> getModuleWithExportedPackages(CtClass moduleInfo) {
        ClassFile classFile = moduleInfo.getClassFile();
        if (!classFile.getName().equals(MODULE_INFO_CLASS_NAME)) {
            throw new IllegalArgumentException("getModuleWithExportedPackages only supports module-info.class");
        }

        ConstPool constPool = classFile.getConstPool();

        byte[] moduleAttribute = classFile.getAttribute("Module").get();

        // The first 2 bytes give the module_name_index, which is needed to get the module name from the constPool
        int attrIdx = 0;
        int moduleNameIndex = moduleAttribute[attrIdx++] << 16;
        moduleNameIndex |= moduleAttribute[attrIdx++];

        String moduleName = constPool.getModuleInfo(moduleNameIndex);
        ArrayList<String> exportedPackages = new ArrayList<>();

        // The next 4 bytes consist of the module_flags and module_version_index, neither of which
        // are relevant here.
        attrIdx += 4;

        // The next 2 bytes are the requires_count
        int requiresCount = moduleAttribute[attrIdx++] << 16;
        requiresCount |= moduleAttribute[attrIdx++];

        // Skip the requires table. Each require structure consists of 6 bytes.
        attrIdx += requiresCount * 6;

        // The next 2 bytes are the exports count
        int exportsCount = moduleAttribute[attrIdx++] << 16;
        exportsCount |= moduleAttribute[attrIdx++];

        for (int i = 0; i < exportsCount; i++) {
            int exportsIndex = moduleAttribute[attrIdx++] << 16;
            exportsIndex = moduleAttribute[attrIdx++];
            String exportedPackageName = constPool.getPackageInfo(exportsIndex).replace('/', '.');
            exportedPackages.add(exportedPackageName);
            // Skip the 2 byte exports_flags
            attrIdx += 2;
            // The next 2 bytes are the exports to count. Need this to skip the exports to table for now, but
            // could use them for better resolution.
            int exportsToCount = moduleAttribute[attrIdx++] << 16;
            exportsToCount |= moduleAttribute[attrIdx++];
            // TODO Eventually check exportedTo to see if this is valid
            // For now, skip each 2 byte exports_to
            attrIdx += 2 + exportsToCount;
        }

        return Optional.of(new Pair<>(moduleName, exportedPackages));
    }
}
