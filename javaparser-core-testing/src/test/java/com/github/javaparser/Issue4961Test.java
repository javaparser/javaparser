package com.github.javaparser;

import static com.github.javaparser.utils.TestUtils.assertNoProblems;

import com.github.javaparser.ast.CompilationUnit;
import org.junit.jupiter.api.Test;

public class Issue4961Test {

    @Test
    public void testIssue4961() {

        String code = """
                // Support JEP 513: Flexible Constructor Bodies
                // https://youtrack.jetbrains.com/projects/IDEA/issues/IDEA-372971/Support-JEP-513-Flexible-Constructor-Bodies
                
                void main(String[] args) {
                    Employee e1 = new Employee(30, "A123");
                    e1.show();
                
                    // Employee Age: 30, Office ID: null
                    // Employee Age: 30, Office ID: A123
                }
                
                class Person {
                    final int age;
                
                    Person(int age) {
                        this.age = age;
                        show();
                    }
                
                    void show() {
                        System.out.println("Age: " + age);
                    }
                }
                
                class Employee extends Person {
                    final String officeId;
                
                    Employee(int age, String officeId) {
                        super(validateAge(age));
                        this.officeId = officeId;
                    }
                
                    private static int validateAge(int age) {
                        if (age < 18 || age > 67)
                            throw new IllegalArgumentException("Invalid age: " + age);
                        return age;
                    }
                
                    @Override
                    void show() {
                        System.out.println("Employee Age: " + age + ", Office ID: " + officeId);
                    }
                }\
                """;

        JavaParser parser = new JavaParser();
        ParseResult<CompilationUnit> result = parser.parse(code);
        assertNoProblems(result);
    }
}
