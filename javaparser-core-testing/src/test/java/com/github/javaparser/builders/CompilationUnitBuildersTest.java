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

package com.github.javaparser.builders;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.body.AnnotationDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.RecordDeclaration;
import com.github.javaparser.ast.expr.Name;
import org.junit.jupiter.api.Test;

import java.lang.annotation.ElementType;
import java.util.Comparator;
import java.util.List;
import java.util.Map;

import static com.github.javaparser.StaticJavaParser.parseImport;
import static com.github.javaparser.ast.Modifier.Keyword.PRIVATE;
import static com.github.javaparser.ast.Modifier.Keyword.PUBLIC;
import static com.github.javaparser.utils.Utils.SYSTEM_EOL;
import static org.junit.jupiter.api.Assertions.*;

class CompilationUnitBuildersTest {
  private final CompilationUnit cu = new CompilationUnit();

  @Test
  void testAddImport() {
    // duplicate imports
    cu.addImport(Map.class);
    cu.addImport(Map.class);
    cu.addImport(Map.class.getCanonicalName());
    cu.addImport(List.class);
    assertEquals(2, cu.getImports().size());

    cu.addImport(com.github.javaparser.StaticJavaParser.class.getCanonicalName() + ".parseImport", true, false);
    assertEquals(3, cu.getImports().size());

    assertEquals("import " + Map.class.getCanonicalName() + ";" + SYSTEM_EOL, cu.getImport(0).toString());
    assertEquals("import " + List.class.getCanonicalName() + ";" + SYSTEM_EOL, cu.getImport(1).toString());
    assertEquals("import static " + com.github.javaparser.StaticJavaParser.class.getCanonicalName() + ".parseImport;" + SYSTEM_EOL,
        cu.getImport(2).toString());
  }

  public class $tartsWith$ {
  }

  @Test
  public void test$ImportStarts() {
    cu.addImport($tartsWith$.class);
    cu.addImport("my.$tartsWith$");
    assertEquals(2, cu.getImports().size());
    assertEquals("import " + $tartsWith$.class.getCanonicalName() + ";" + SYSTEM_EOL, cu.getImport(0).toString());
    assertEquals("import my.$tartsWith$;" + SYSTEM_EOL, cu.getImport(1).toString());
  }

  public class F$F {
  }

  @Test
  public void test$Import() {
    cu.addImport(F$F.class);
    cu.addImport("my.F$F");
    // doesnt fail, but imports class "F.F"
    assertEquals(2, cu.getImports().size());
    assertEquals("import " + F$F.class.getCanonicalName() + ";" + SYSTEM_EOL, cu.getImport(0).toString());
    assertEquals("import my.F$F;" + SYSTEM_EOL, cu.getImport(1).toString());
  }

  @Test
  void ignoreJavaLangImports() {
    cu.addImport("java.lang.Long");
    cu.addImport("java.lang.*");
    cu.addImport(String.class);
    assertEquals(0, cu.getImports().size());
  }

  @Test
  void ignoreImportsWithinSamePackage() {
    cu.setPackageDeclaration(new PackageDeclaration(new Name(new Name("one"), "two")));
    cu.addImport("one.two.IgnoreImportWithinSamePackage");
    assertEquals(0, cu.getImports().size());
    cu.addImport("one.two.three.DoNotIgnoreImportWithinSubPackage");
    assertEquals(1, cu.getImports().size());
    assertEquals("import one.two.three.DoNotIgnoreImportWithinSubPackage;" + SYSTEM_EOL, cu.getImport(0).toString());
  }

  @Test
  void throwIllegalArgumentExceptionOnImportingAnonymousClass() {
    assertThrows(IllegalArgumentException.class, () -> cu.addImport(new Comparator<Long>() {

      @Override
      public int compare(Long o1, Long o2) {
        return o1.compareTo(o2);
      }
    }.getClass()));
  }

  @Test
  void throwIllegalArgumentExceptionOnImportingLocalClass() {
    class LocalClass implements Comparator<Long> {

      @Override
      public int compare(Long o1, Long o2) {
        return o1.compareTo(o2);
      }
    }
    Class<?> localClass = LocalClass.class;
    assertThrows(IllegalArgumentException.class, () -> cu.addImport(localClass));
  }

  @Test
  void ignoreImportsOfDefaultPackageClasses() {
    cu.addImport("MyImport");
    assertEquals(0, cu.getImports().size());
  }

  @Test
  void duplicateByAsterisk() {
    // check asterisk imports
    cu.addImport("my", false, true);
    cu.addImport("my.Import");
    cu.addImport("my.AnotherImport");
    cu.addImport("my.other.Import");
    assertEquals(2, cu.getImports().size());
    assertEquals("import my.*;" + SYSTEM_EOL, cu.getImport(0).toString());
    assertEquals("import my.other.Import;" + SYSTEM_EOL, cu.getImport(1).toString());
    cu.addImport("my.other.*");
    assertEquals(2, cu.getImports().size());
    assertEquals("import my.*;" + SYSTEM_EOL, cu.getImport(0).toString());
    assertEquals("import my.other.*;" + SYSTEM_EOL, cu.getImport(1).toString());
  }

  @Test
  void typesInTheJavaLangPackageDoNotNeedExplicitImports() {
    cu.addImport(String.class);
    assertEquals(0, cu.getImports().size());
  }

  @Test
  void typesInSubPackagesOfTheJavaLangPackageRequireExplicitImports() {
    cu.addImport(ElementType.class);
    assertEquals(1, cu.getImports().size());
    assertEquals("import java.lang.annotation.ElementType;" + SYSTEM_EOL, cu.getImport(0).toString());
  }

  @Test
  void doNotAddDuplicateImportsByClass() {
    cu.addImport(Map.class);
    cu.addImport(Map.class);
    assertEquals(1, cu.getImports().size());
  }

  @Test
  void doNotAddDuplicateImportsByString() {
    cu.addImport(Map.class);
    cu.addImport("java.util.Map");
    assertEquals(1, cu.getImports().size());
  }

  @Test
  void doNotAddDuplicateImportsByStringAndFlags() {
    cu.addImport(Map.class);
    cu.addImport("java.util.Map", false, false);
    assertEquals(1, cu.getImports().size());
  }

  @Test
  void doNotAddDuplicateImportsByImportDeclaration() {
    cu.addImport(Map.class);
    cu.addImport(parseImport("import java.util.Map;"));
    assertEquals(1, cu.getImports().size());
  }

  @Test
  void testAddImportArrayTypes() {
    cu.addImport(CompilationUnit[][][].class);
    cu.addImport(int[][][].class);
    cu.addImport(Integer[][][].class);
    cu.addImport(List[][][].class);
    assertEquals(2, cu.getImports().size());
    assertEquals("com.github.javaparser.ast.CompilationUnit", cu.getImport(0).getNameAsString());
    assertEquals("java.util.List", cu.getImport(1).getNameAsString());
  }

  class testInnerClass {

  }

  @Test
  void testAddImportAnonymousClass() {
    cu.addImport(testInnerClass.class);
    assertEquals("import " + testInnerClass.class.getCanonicalName().replace("$", ".") + ";" + SYSTEM_EOL,
        cu.getImport(0).toString());
  }

  @Test
  void testAddClass() {
    ClassOrInterfaceDeclaration myClassDeclaration = cu.addClass("testClass", PRIVATE);
    assertEquals(1, cu.getTypes().size());
    assertEquals("testClass", cu.getType(0).getNameAsString());
    assertEquals(ClassOrInterfaceDeclaration.class, cu.getType(0).getClass());
    assertTrue(myClassDeclaration.isPrivate());
    assertFalse(myClassDeclaration.isInterface());
  }

  @Test
  void testAddInterface() {
    ClassOrInterfaceDeclaration myInterfaceDeclaration = cu.addInterface("testInterface");
    assertEquals(1, cu.getTypes().size());
    assertEquals("testInterface", cu.getType(0).getNameAsString());
    assertTrue(myInterfaceDeclaration.isPublic());
    assertEquals(ClassOrInterfaceDeclaration.class, cu.getType(0).getClass());
    assertTrue(myInterfaceDeclaration.isInterface());
  }

  @Test
  void testAddEnum() {
    EnumDeclaration myEnumDeclaration = cu.addEnum("test");
    assertEquals(1, cu.getTypes().size());
    assertEquals("test", cu.getType(0).getNameAsString());
    assertTrue(myEnumDeclaration.isPublic());
    assertEquals(EnumDeclaration.class, cu.getType(0).getClass());
  }

  @Test
  void testAddAnnotationDeclaration() {
    AnnotationDeclaration myAnnotationDeclaration = cu.addAnnotationDeclaration("test");
    assertEquals(1, cu.getTypes().size());
    assertEquals("test", cu.getType(0).getNameAsString());
    assertTrue(myAnnotationDeclaration.isPublic());
    assertEquals(AnnotationDeclaration.class, cu.getType(0).getClass());
  }

  @Test
  void testAddTypeWithRecordDeclaration() {
    RecordDeclaration myRecordDeclaration = new RecordDeclaration(Modifier.createModifierList(PUBLIC), "test");
    cu.addType(myRecordDeclaration);
    assertEquals(1, cu.getTypes().size());
    assertEquals("test", cu.getType(0).getNameAsString());
    assertTrue(myRecordDeclaration.isPublic());
    assertTrue(myRecordDeclaration.isFinal());
    assertEquals(RecordDeclaration.class, cu.getType(0).getClass());
  }

  @Test
  void testGetClassByName() {
    assertEquals(cu.addClass("test"), cu.getClassByName("test").get());
  }

  @Test
  void testGetInterfaceByName() {
    assertEquals(cu.addInterface("test"), cu.getInterfaceByName("test").get());
  }

  @Test
  void testGetEnumByName() {
    assertEquals(cu.addEnum("test"), cu.getEnumByName("test").get());
  }

  @Test
  void testGetAnnotationDeclarationByName() {
    assertEquals(cu.addAnnotationDeclaration("test"), cu.getAnnotationDeclarationByName("test").get());
  }

  @Test
  void testGetRecordByName() {
    assertEquals(cu.addType(new RecordDeclaration(Modifier.createModifierList(), "test")).getType(0),
            cu.getRecordByName("test").get());
  }
}
