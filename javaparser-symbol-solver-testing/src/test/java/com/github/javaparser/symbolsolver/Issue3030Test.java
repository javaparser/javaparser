/*
 * Copyright (C) 2013-2023 The JavaParser Team.
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

package com.github.javaparser.symbolsolver;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.util.Optional;
import java.util.Spliterator;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class Issue3030Test extends AbstractResolutionTest {

    @Test
    public void test3030() {
        String sourceCode = "package com.example;\n" +
                "\n" +
                "import java.util.Comparator;\n" +
                "import java.util.Spliterator;\n" +
                "import java.util.function.Consumer;\n" +
                "import java.util.function.IntConsumer;\n" +
                "import java.util.function.IntFunction;\n" +
                "import java.util.stream.IntStream;\n" +
                "\n" +
                "public class TestClass {\n" +
                "\n" +
                "    static <T> Spliterator<T> indexed(int size, int extraCharacteristics, IntFunction<T> function, Comparator<? super T> comparator) {\n" +
                "        class WithCharacteristics implements Spliterator<T> {\n" +
                "\n" +
                "            private final Spliterator.OfInt delegate;\n" +
                "\n" +
                "            WithCharacteristics(Spliterator.OfInt delegate) {\n" +
                "                this.delegate = delegate;\n" +
                "            }\n" +
                "\n" +
                "            @Override\n" +
                "            public boolean tryAdvance(Consumer<? super T> action) {\n" +
                "                return delegate.tryAdvance((IntConsumer) i -> action.accept(function.apply(i)));\n" +
                "            }\n" +
                "\n" +
                "            @Override\n" +
                "            public void forEachRemaining(Consumer<? super T> action) {\n" +
                "                delegate.forEachRemaining((IntConsumer) i -> action.accept(function.apply(i)));\n" +
                "            }\n" +
                "\n" +
                "            @Override\n" +
                "            public Spliterator<T> trySplit() {\n" +
                "                Spliterator.OfInt split = delegate.trySplit();\n" +
                "                return (split == null) ? null : new WithCharacteristics(split);\n" +
                "            }\n" +
                "\n" +
                "            @Override\n" +
                "            public long estimateSize() {\n" +
                "                return delegate.estimateSize();\n" +
                "            }\n" +
                "\n" +
                "            @Override\n" +
                "            public int characteristics() {\n" +
                "                return Spliterator.ORDERED | Spliterator.SIZED | Spliterator.SUBSIZED | extraCharacteristics;\n" +
                "            }\n" +
                "\n" +
                "            @Override\n" +
                "            public Comparator<? super T> getComparator() {\n" +
                "                if (hasCharacteristics(Spliterator.SORTED)) {\n" +
                "                    return comparator;\n" +
                "                } else {\n" +
                "                    throw new IllegalStateException();\n" +
                "                }\n" +
                "            }\n" +
                "        }\n" +
                "        return new WithCharacteristics(IntStream.range(0, size).spliterator());\n" +
                "    }\n" +
                "\n" +
                "}\n";

        ReflectionTypeSolver reflectionSolver = new ReflectionTypeSolver();
        JavaSymbolSolver symbolSolver = new JavaSymbolSolver(reflectionSolver);
        StaticJavaParser.getConfiguration()
                .setSymbolResolver(symbolSolver);

        CompilationUnit cu = StaticJavaParser.parse(sourceCode);
        Optional<FieldDeclaration> optionalFieldDeclaration = cu.findFirst(FieldDeclaration.class);
        assertTrue(optionalFieldDeclaration.isPresent());

        ResolvedType resolvedField = optionalFieldDeclaration.get().resolve().getType();
        assertEquals(Spliterator.OfInt.class.getCanonicalName(), resolvedField.asReferenceType().getQualifiedName());
    }

}
