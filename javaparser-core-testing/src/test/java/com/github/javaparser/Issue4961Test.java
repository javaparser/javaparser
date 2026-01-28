package com.github.javaparser;

import static com.github.javaparser.utils.TestUtils.assertNoProblems;

import com.github.javaparser.ast.CompilationUnit;
import org.junit.jupiter.api.Test;

public class Issue4961Test {

    @Test
    public void testIssue4961() {

        String code = "// Support JEP 513: Flexible Constructor Bodies\n"
                + "// https://youtrack.jetbrains.com/projects/IDEA/issues/IDEA-372971/Support-JEP-513-Flexible-Constructor-Bodies\n"
                + "\n"
                + "void main(String[] args) {\n"
                + "    Employee e1 = new Employee(30, \"A123\");\n"
                + "    e1.show();\n"
                + "\n"
                + "    // Employee Age: 30, Office ID: null\n"
                + "    // Employee Age: 30, Office ID: A123\n"
                + "}\n"
                + "\n"
                + "class Person {\n"
                + "    final int age;\n"
                + "\n"
                + "    Person(int age) {\n"
                + "        this.age = age;\n"
                + "        show();\n"
                + "    }\n"
                + "\n"
                + "    void show() {\n"
                + "        System.out.println(\"Age: \" + age);\n"
                + "    }\n"
                + "}\n"
                + "\n"
                + "class Employee extends Person {\n"
                + "    final String officeId;\n"
                + "\n"
                + "    Employee(int age, String officeId) {\n"
                + "        super(validateAge(age));\n"
                + "        this.officeId = officeId;\n"
                + "    }\n"
                + "\n"
                + "    private static int validateAge(int age) {\n"
                + "        if (age < 18 || age > 67)\n"
                + "            throw new IllegalArgumentException(\"Invalid age: \" + age);\n"
                + "        return age;\n"
                + "    }\n"
                + "\n"
                + "    @Override\n"
                + "    void show() {\n"
                + "        System.out.println(\"Employee Age: \" + age + \", Office ID: \" + officeId);\n"
                + "    }\n"
                + "}";

        JavaParser parser = new JavaParser();
        ParseResult<CompilationUnit> result = parser.parse(code);
        assertNoProblems(result);
    }
}
