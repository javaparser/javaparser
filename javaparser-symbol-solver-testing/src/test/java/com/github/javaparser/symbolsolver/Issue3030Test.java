/*
 * Copyright (C) 2013-2026 The JavaParser Team.
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

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.util.Optional;
import java.util.Spliterator;
import org.junit.jupiter.api.Test;

public class Issue3030Test extends AbstractResolutionTest {

    @Test
    public void test3030() {
        String sourceCode = """
                package com.example;
                
                import java.util.Comparator;
                import java.util.Spliterator;
                import java.util.function.Consumer;
                import java.util.function.IntConsumer;
                import java.util.function.IntFunction;
                import java.util.stream.IntStream;
                
                public class TestClass {
                
                    static <T> Spliterator<T> indexed(int size, int extraCharacteristics, IntFunction<T> function, Comparator<? super T> comparator) {
                        class WithCharacteristics implements Spliterator<T> {
                
                            private final Spliterator.OfInt delegate;
                
                            WithCharacteristics(Spliterator.OfInt delegate) {
                                this.delegate = delegate;
                            }
                
                            @Override
                            public boolean tryAdvance(Consumer<? super T> action) {
                                return delegate.tryAdvance((IntConsumer) i -> action.accept(function.apply(i)));
                            }
                
                            @Override
                            public void forEachRemaining(Consumer<? super T> action) {
                                delegate.forEachRemaining((IntConsumer) i -> action.accept(function.apply(i)));
                            }
                
                            @Override
                            public Spliterator<T> trySplit() {
                                Spliterator.OfInt split = delegate.trySplit();
                                return (split == null) ? null : new WithCharacteristics(split);
                            }
                
                            @Override
                            public long estimateSize() {
                                return delegate.estimateSize();
                            }
                
                            @Override
                            public int characteristics() {
                                return Spliterator.ORDERED | Spliterator.SIZED | Spliterator.SUBSIZED | extraCharacteristics;
                            }
                
                            @Override
                            public Comparator<? super T> getComparator() {
                                if (hasCharacteristics(Spliterator.SORTED)) {
                                    return comparator;
                                } else {
                                    throw new IllegalStateException();
                                }
                            }
                        }
                        return new WithCharacteristics(IntStream.range(0, size).spliterator());
                    }
                
                }
                """;

        ReflectionTypeSolver reflectionSolver = new ReflectionTypeSolver();
        JavaSymbolSolver symbolSolver = new JavaSymbolSolver(reflectionSolver);
        StaticJavaParser.getConfiguration().setSymbolResolver(symbolSolver);

        CompilationUnit cu = StaticJavaParser.parse(sourceCode);
        Optional<FieldDeclaration> optionalFieldDeclaration = cu.findFirst(FieldDeclaration.class);
        assertTrue(optionalFieldDeclaration.isPresent());

        ResolvedType resolvedField = optionalFieldDeclaration.get().resolve().getType();
        assertEquals(
                Spliterator.OfInt.class.getCanonicalName(),
                resolvedField.asReferenceType().getQualifiedName());
    }
}
