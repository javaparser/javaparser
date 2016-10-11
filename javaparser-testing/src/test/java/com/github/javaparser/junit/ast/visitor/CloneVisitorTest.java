package com.github.javaparser.junit.ast.visitor;
import static org.junit.Assert.assertEquals;

import com.github.javaparser.ast.NodeList;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.body.AnnotationDeclaration;
import com.github.javaparser.ast.body.EmptyTypeDeclaration;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.AnnotationMemberDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.EmptyMemberDeclaration;
import com.github.javaparser.ast.body.EnumConstantDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.InitializerDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

public class CloneVisitorTest{
	CompilationUnit cu;
	
	@Before
	public void setUp(){
		cu = new CompilationUnit();
	}
	
	@After
	public void teardown() {
		cu = null;
	}
	
	@Test
	public void cloneJavaDocTest(){

		List<BodyDeclaration<?>> bodyDeclarationList = new ArrayList<BodyDeclaration<?>>();
		bodyDeclarationList.add(new AnnotationMemberDeclaration().setJavaDocComment("javadoc"));
		bodyDeclarationList.add(new ConstructorDeclaration().setJavaDocComment("javadoc"));
		bodyDeclarationList.add(new EmptyMemberDeclaration().setJavaDocComment("javadoc"));
		bodyDeclarationList.add(new EnumConstantDeclaration().setJavaDocComment("javadoc"));
		bodyDeclarationList.add(new FieldDeclaration().setJavaDocComment("javadoc"));
		bodyDeclarationList.add(new InitializerDeclaration().setJavaDocComment("javadoc"));
		bodyDeclarationList.add(new MethodDeclaration().setJavaDocComment("javadoc"));
		
		NodeList<TypeDeclaration<?>> typeDeclarationList = new NodeList<>();
		AnnotationDeclaration annotationDeclaration = new AnnotationDeclaration();
		annotationDeclaration.setName("nnotationDeclarationTest");
		typeDeclarationList.add(annotationDeclaration.setJavaDocComment("javadoc"));
		
		EmptyTypeDeclaration emptyTypeDeclaration = new EmptyTypeDeclaration();
		emptyTypeDeclaration.setName("emptyTypeDeclarationTest");
		typeDeclarationList.add(emptyTypeDeclaration.setJavaDocComment("javadoc"));
		
		EnumDeclaration enumDeclaration = new EnumDeclaration();
		enumDeclaration.setName("enumDeclarationTest");
		typeDeclarationList.add(enumDeclaration.setJavaDocComment("javadoc"));
		
		ClassOrInterfaceDeclaration classOrInterfaceDeclaration = new ClassOrInterfaceDeclaration();
		classOrInterfaceDeclaration.setName("classOrInterfaceDeclarationTest");
		typeDeclarationList.add(classOrInterfaceDeclaration.setJavaDocComment("javadoc"));
		
		EmptyTypeDeclaration emptyTypeDeclaration1 = new EmptyTypeDeclaration();
		emptyTypeDeclaration1.setName("emptyTypeDeclarationTest1");
		typeDeclarationList.add(emptyTypeDeclaration.setMembers(bodyDeclarationList));
		
		cu.setTypes(typeDeclarationList);
		CompilationUnit cuClone=(CompilationUnit) new CloneVisitor().visit(cu, null);
		
		NodeList<TypeDeclaration<?>> typeDeclarationListClone = cuClone.getTypes();
		Iterator<TypeDeclaration<?>> typeItr = typeDeclarationListClone.iterator();
		TypeDeclaration<?>  typeDeclaration;
		while(typeItr.hasNext()){
			typeDeclaration = typeItr.next();
			if(typeDeclaration.getMembers()==null){
				assertEquals(typeDeclaration.getComment().getContent(),"javadoc");
			}else{
				Iterator<BodyDeclaration<?>> bodyItr = typeDeclaration.getMembers().iterator();
				while(bodyItr.hasNext()){
					BodyDeclaration<?> bodyDeclaration = bodyItr.next();
					assertEquals(bodyDeclaration.getComment().getContent(),"javadoc");
				}
			}
		}
		
	}
	
}
