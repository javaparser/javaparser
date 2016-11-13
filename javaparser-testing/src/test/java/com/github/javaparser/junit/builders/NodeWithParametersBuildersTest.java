package com.github.javaparser.junit.builders;

import static org.junit.Assert.assertEquals;

import java.util.List;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;

public class NodeWithParametersBuildersTest {
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
	public void testAddParameter() {
		MethodDeclaration addMethod = cu.addClass("test").addMethod("foo", Modifier.PUBLIC);
		addMethod.addParameter(int.class, "yay");
		Parameter myNewParam = addMethod.addAndGetParameter(List.class, "myList");
		assertEquals(1, cu.getImportsList().size());
		assertEquals("import " + List.class.getName() + ";" + System.getProperty("line.separator"), cu.getImportsList().get(0).toString());
		assertEquals(2, addMethod.getParametersList().size());
		assertEquals("yay", addMethod.getParametersList().get(0).getName());
		assertEquals("List", addMethod.getParametersList().get(1).getType().toString());
		assertEquals(myNewParam, addMethod.getParametersList().get(1));
	}

	@Test
	public void testGetParamByName() {
		MethodDeclaration addMethod = cu.addClass("test").addMethod("foo", Modifier.PUBLIC);
		Parameter addAndGetParameter = addMethod.addAndGetParameter(int.class, "yay");
		assertEquals(addAndGetParameter, addMethod.getParamByName("yay"));
	}

	@Test
	public void testGetParamByType() {
		MethodDeclaration addMethod = cu.addClass("test").addMethod("foo", Modifier.PUBLIC);
		Parameter addAndGetParameter = addMethod.addAndGetParameter(int.class, "yay");
		assertEquals(addAndGetParameter, addMethod.getParamByType("int"));
		assertEquals(addAndGetParameter, addMethod.getParamByType(int.class));
	}

}
