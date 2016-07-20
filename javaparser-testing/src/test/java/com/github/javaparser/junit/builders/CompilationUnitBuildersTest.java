package com.github.javaparser.junit.builders;

import static org.junit.Assert.assertEquals;

import java.util.List;
import java.util.Map;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import com.github.javaparser.ast.CompilationUnit;

public class CompilationUnitBuildersTest {
	CompilationUnit cu;

	@Before
	public void setup() {
		cu = new CompilationUnit();
	}

	@After
	public void teardown() {
		cu = null;
	}

	@Test
	public void testAddImport() {
		cu.addImport(Map.class);
		cu.addImport(Map.class);
		cu.addImport(List.class);
		assertEquals(2, cu.getImports().size());
		cu.addImport("myImport");
		assertEquals(3, cu.getImports().size());
		assertEquals("import " + Map.class.getName() + ";" + System.getProperty("line.separator"), cu.getImports().get(0).toString());
		assertEquals("import " + List.class.getName() + ";" + System.getProperty("line.separator"), cu.getImports().get(1).toString());
		assertEquals("import myImport;" + System.getProperty("line.separator"), cu.getImports().get(2).toString());
	}

	/*
	
	Scenario:  A CompilationUnit in which we add a class with addClass(String name)
	
	Then the expected source should be:
	TODO
	
	Scenario:  A CompilationUnit in which we add a class with addClass(String name, EnumSet<Modifier> modifiers)
	
	Then the expected source should be:
	TODO
	
		
	Scenario:  A CompilationUnit in which we addInterface(String name) 
	Scenario:  A CompilationUnit in which we addInterface(String name, EnumSet<Modifier> modifiers) 
	
	Scenario:  A CompilationUnit in which we addEnum(String name) 
	Scenario:  A CompilationUnit in which we addEnum(String name, EnumSet<Modifier> modifiers) 
	
	Scenario:  A CompilationUnit in which we addAnnotationDeclaration(String name) 
	Scenario:  A CompilationUnit in which we addAnnotationDeclaration(String name, EnumSet<Modifier> modifiers) 
	
	Scenario:  A CompilationUnit in which we getClassByName(String className) 
	Scenario:  A CompilationUnit in which we getInterfaceByName(String interfaceName) 
	Scenario:  A CompilationUnit in which we getEnumByName(String enumName) 
	Scenario:  A CompilationUnit in which we getAnnotationDeclarationByName(String annotationName) 
	
	*/
}
