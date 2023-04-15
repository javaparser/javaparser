/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.observer.AstObserver;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.printer.lexicalpreservation.AbstractLexicalPreservingTest;
import com.github.javaparser.printer.lexicalpreservation.LexicalPreservingPrinter;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import java.util.*;

import static com.github.javaparser.ast.NodeList.nodeList;
import static org.junit.jupiter.api.Assertions.*;

class NodeListTest extends AbstractLexicalPreservingTest {

    @Test
    void replace() {
        final NodeList<Name> list = nodeList(new Name("a"), new Name("b"), new Name("c"));

        final boolean replaced = list.replace(new Name("b"), new Name("z"));

        assertTrue(replaced);
        assertEquals(3, list.size());
        assertEquals("a", list.get(0).asString());
        assertEquals("z", list.get(1).asString());
        assertEquals("c", list.get(2).asString());
    }

    @Test
    void toStringTest() {
        final NodeList<Name> list = nodeList(new Name("abc"), new Name("bcd"), new Name("cde"));

        assertEquals(3, list.size());
        assertEquals("[abc, bcd, cde]", list.toString());
    }

    @Test
    void addFirst() {
        final NodeList<Name> list = nodeList(new Name("abc"), new Name("bcd"), new Name("cde"));

        list.addFirst(new Name("xxx"));

        assertEquals(4, list.size());
        assertEquals("[xxx, abc, bcd, cde]", list.toString());
    }

    @Test
    void addLast() {
        final NodeList<Name> list = nodeList(new Name("abc"), new Name("bcd"), new Name("cde"));

        list.addLast(new Name("xxx"));

        assertEquals(4, list.size());
        assertEquals("[abc, bcd, cde, xxx]", list.toString());
    }

    @Test
    void addBefore() {
        Name n = new Name("bcd");
        final NodeList<Name> list = nodeList(new Name("abc"), n, new Name("cde"));

        list.addBefore(new Name("xxx"), n);

        assertEquals(4, list.size());
        assertEquals("[abc, xxx, bcd, cde]", list.toString());
    }

    @Test
    void addAfter() {
        Name n = new Name("bcd");
        final NodeList<Name> list = nodeList(new Name("abc"), n, new Name("cde"));

        list.addAfter(new Name("xxx"), n);

        assertEquals(4, list.size());
        assertEquals("[abc, bcd, xxx, cde]", list.toString());
    }

    @Test
    void addBeforeFirst() {
        Name abc = new Name("abc");
        final NodeList<Name> list = nodeList(abc, new Name("bcd"), new Name("cde"));

        list.addBefore(new Name("xxx"), abc);

        assertEquals(4, list.size());
        assertEquals("[xxx, abc, bcd, cde]", list.toString());
    }

    @Test
    void addAfterLast() {
        Name cde = new Name("cde");
        final NodeList<Name> list = nodeList(new Name("abc"), new Name("bcd"), cde);

        list.addAfter(new Name("xxx"), cde);

        assertEquals(4, list.size());
        assertEquals("[abc, bcd, cde, xxx]", list.toString());
    }


    @Test
    public void getFirstWhenEmpty() {
        final NodeList<Name> list = nodeList();

        Optional<Name> first = list.getFirst();

        assertFalse(first.isPresent());
        assertEquals("Optional.empty", first.toString());
    }

    @Test
    public void getFirstWhenNonEmpty() {
        final NodeList<Name> list = nodeList(new Name("abc"), new Name("bcd"), new Name("cde"));

        Optional<Name> first = list.getFirst();

        assertTrue(first.isPresent());
        assertEquals("Optional[abc]", first.toString());
    }

    @Test
    public void getLastWhenEmpty() {
        final NodeList<Name> list = nodeList();

        Optional<Name> last = list.getLast();

        assertFalse(last.isPresent());
        assertEquals("Optional.empty", last.toString());
    }

    @Test
    public void getLastWhenNonEmpty() {
        final NodeList<Name> list = nodeList(new Name("abc"), new Name("bcd"), new Name("cde"));

        Optional<Name> last = list.getLast();

        assertTrue(last.isPresent());
        assertEquals("Optional[cde]", last.toString());
    }

    @Nested
    class IteratorTest {

        @Nested
        class ObserversTest {
            NodeList<Name> list;
            ListIterator<Name> iterator;

            List<String> propertyChanges;
            List<String> parentChanges;
            List<String> listChanges;
            List<String> listReplacements;
            AstObserver testObserver = new AstObserver() {
                @Override
                public void propertyChange(Node observedNode, ObservableProperty property, Object oldValue, Object newValue) {
                    propertyChanges.add(String.format("%s.%s changed from %s to %s", observedNode.getClass().getSimpleName(), property.name().toLowerCase(), oldValue, newValue));
                }

                @Override
                public void parentChange(Node observedNode, Node previousParent, Node newParent) {
                    parentChanges.add(String.format("%s 's parent changed from %s to %s", observedNode.getClass().getSimpleName(), previousParent, newParent));
                }

                @Override
                public void listChange(NodeList<?> observedNode, ListChangeType type, int index, Node nodeAddedOrRemoved) {
                    listChanges.add(String.format("%s %s to/from %s at position %d", nodeAddedOrRemoved.getClass().getSimpleName(), type.name(), observedNode.getClass().getSimpleName(), index));
                }

                @Override
                public void listReplacement(NodeList<?> observedNode, int index, Node oldNode, Node newNode) {
                    listReplacements.add(String.format("%s replaced within %s at position %d", newNode.getClass().getSimpleName(), observedNode.getClass().getSimpleName(), index));
                }

            };

            @BeforeEach
            void pre() {
                list = nodeList();
                list.register(testObserver);
                iterator = list.listIterator();

                propertyChanges = new ArrayList<>();
                parentChanges = new ArrayList<>();
                listChanges = new ArrayList<>();
                listReplacements = new ArrayList<>();
            }

            @Test
            void whenAdd() {
                assertEquals(0, propertyChanges.size());
                assertEquals(0, parentChanges.size());
                assertEquals(0, listChanges.size());
                assertEquals(0, listReplacements.size());

                iterator.add(new Name("abc"));

                assertEquals(0, propertyChanges.size());
                assertEquals(0, parentChanges.size());
                assertEquals(1, listChanges.size());
                assertEquals(0, listReplacements.size());

                assertEquals("Name ADDITION to/from NodeList at position 0", listChanges.get(0));
            }

            @Test
            void whenRemove() {
                iterator.add(new Name("abc"));

                assertEquals(0, propertyChanges.size());
                assertEquals(0, parentChanges.size());
                assertEquals(1, listChanges.size());
                assertEquals(0, listReplacements.size());

                iterator.previous();
                iterator.remove();

                assertEquals(0, propertyChanges.size());
                assertEquals(0, parentChanges.size());
                assertEquals(2, listChanges.size());
                assertEquals(0, listReplacements.size());

                assertEquals("Name ADDITION to/from NodeList at position 0", listChanges.get(0));
                assertEquals("Name REMOVAL to/from NodeList at position 0", listChanges.get(1));
            }

            @Test
            void whenSet() {
                iterator.add(new Name("abc"));

                assertEquals(0, propertyChanges.size());
                assertEquals(0, parentChanges.size());
                assertEquals(1, listChanges.size());
                assertEquals(0, listReplacements.size());

                iterator.previous();
                iterator.set(new Name("xyz"));

                assertEquals(0, propertyChanges.size());
                assertEquals(0, parentChanges.size());
                assertEquals(1, listChanges.size());
                assertEquals(1, listReplacements.size());

                assertEquals("Name ADDITION to/from NodeList at position 0", listChanges.get(0));
                assertEquals("Name replaced within NodeList at position 0", listReplacements.get(0));
            }


            @Test
            void usageTest() {
                final String REFERENCE_TO_BE_DELETED = "bad";
                considerCode("" +
                        "@MyAnnotation(myElements = {\"good\", \"bad\", \"ugly\"})\n" +
                        "public final class MyClass {\n" +
                        "}");
                String expected = "" +
                        "@MyAnnotation(myElements = {\"good\", \"ugly\"})\n" +
                        "public final class MyClass {\n" +
                        "}";

                List<NormalAnnotationExpr> annotations = cu.findAll(NormalAnnotationExpr.class);

                annotations.forEach(annotation -> {
                    // testcase, per https://github.com/javaparser/javaparser/issues/2936#issuecomment-731370505
                    MemberValuePair mvp = annotation.getPairs().get(0);
                    Expression value = mvp.getValue();
                    if ((value instanceof ArrayInitializerExpr)) {
                        NodeList<Expression> myElements = ((ArrayInitializerExpr) value).getValues();

                        for (Iterator<Expression> iterator = myElements.iterator(); iterator.hasNext(); ) {
                            Node elt = iterator.next();
                            {
                                String nameAsString = ((StringLiteralExpr) elt).asString();
                                if (REFERENCE_TO_BE_DELETED.equals(nameAsString))
                                    iterator.remove();
                            }
                        }
                    }
                });

                assertEquals(expected, LexicalPreservingPrinter.print(cu));
            }
        }

        @Nested
        class AddRemoveListIteratorTest {
            NodeList<Name> list;
            ListIterator<Name> iterator;

            @BeforeEach
            void pre() {
                list = nodeList();
                iterator = list.listIterator();
            }

            @Test
            void whenAdd() {
                assertFalse(iterator.hasNext());
                assertFalse(iterator.hasPrevious());
                // Note that the element is added before the current cursor, thus is accessible via "previous"
                iterator.add(new Name("abc"));
                assertFalse(iterator.hasNext());
                assertTrue(iterator.hasPrevious());
            }

        }

        @Nested
        class EmptyIteratorTest {
            NodeList<Name> list;
            ListIterator<Name> iterator;

            @BeforeEach
            void pre() {
                list = nodeList();
                iterator = list.listIterator();
            }

            @Test
            void whenNext() {
                assertThrows(NoSuchElementException.class, () -> {
                    iterator.next();
                });
            }

            @Test
            void whenHasNext() {
                assertFalse(iterator.hasNext());
            }

            @Test
            void whenAdd() {
                assertFalse(iterator.hasNext());
                assertFalse(iterator.hasPrevious());
                // Note that the element is added before the current cursor, thus is accessible via "previous"
                iterator.add(new Name("abc"));
                assertFalse(iterator.hasNext());
                assertTrue(iterator.hasPrevious());
            }

            @Test
            void whenSet() {
                assertFalse(iterator.hasNext());
                assertFalse(iterator.hasPrevious());
                assertThrows(IllegalArgumentException.class, () -> {
                    // Note that the cursor is initially at -1, thus not possible to set the value here
                    iterator.set(new Name("abc"));
                });
                // Assert that next/previous are still empty
                assertFalse(iterator.hasNext());
                assertFalse(iterator.hasPrevious());
            }

        }

        @Nested
        class SingleItemIteratorTest {
            NodeList<Name> list;
            Iterator<Name> iterator;

            @BeforeEach
            void pre() {
                list = nodeList(new Name("abc"));
                iterator = list.iterator();
            }

            @Test
            void whenNext() {
                Name next = iterator.next();
                assertNotNull(next);
            }

            @Test
            void whenHasNext() {
                assertTrue(iterator.hasNext());
            }

            @Test
            void whenHasNextRepeated() {
                assertTrue(iterator.hasNext());
                assertTrue(iterator.hasNext());
                assertTrue(iterator.hasNext());
                assertTrue(iterator.hasNext());
            }

            @Test
            void whenHasNextThenNext() {
                assertTrue(iterator.hasNext());
                iterator.next();
                assertFalse(iterator.hasNext());
                assertThrows(NoSuchElementException.class, () -> {
                    iterator.next();
                });
            }

            @Test
            void whenRemove() {
                Name current = iterator.next();
                iterator.remove();
                assertFalse(iterator.hasNext());
                assertThrows(NoSuchElementException.class, () -> {
                    iterator.next();
                });
            }

        }
    }
}
