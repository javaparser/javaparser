package com.github.javaparser.printer.lexicalpreservation.changes;

import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.type.ClassOrInterfaceType;

class NoChangeTest {

    @BeforeAll
    static void setUpBeforeClass() throws Exception {
    }

    @AfterAll
    static void tearDownAfterClass() throws Exception {
    }

    @BeforeEach
    void setUp() throws Exception {
    }

    @AfterEach
    void tearDown() throws Exception {
    }
    
    @Test
    void getValue_WithMethodFound() {
        Object o = new NoChange().getValue(ObservableProperty.ANNOTATIONS, new ClassOrInterfaceType());
        assertNotNull(o);
    }

    @Test
    void getValue_WithNoMethodFound() {
        assertThrows(RuntimeException.class, () -> {
            new NoChange().getValue(ObservableProperty.IMPORTS, new ClassOrInterfaceType());
        }, "RuntimeException was expected");
    }
    
}
