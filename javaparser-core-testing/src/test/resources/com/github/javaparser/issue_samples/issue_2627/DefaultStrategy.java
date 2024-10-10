/*
 *  Licensed to the Apache Software Foundation (ASF) under one
 *  or more contributor license agreements.  See the NOTICE file
 *  distributed with this work for additional information
 *  regarding copyright ownership.  The ASF licenses this file
 *  to you under the Apache License, Version 2.0 (the
 *  "License"); you may not use this file except in compliance
 *  with the License.  You may obtain a copy of the License at
 *
 *    http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing,
 *  software distributed under the License is distributed on an
 *  "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 *  KIND, either express or implied.  See the License for the
 *  specific language governing permissions and limitations
 *  under the License.
 */
package groovy.transform.builder;

import groovy.transform.Undefined;
import org.codehaus.groovy.ast.AnnotatedNode;
import org.codehaus.groovy.ast.AnnotationNode;
import org.codehaus.groovy.ast.ClassNode;
import org.codehaus.groovy.ast.ConstructorNode;
import org.codehaus.groovy.ast.FieldNode;
import org.codehaus.groovy.ast.InnerClassNode;
import org.codehaus.groovy.ast.MethodNode;
import org.codehaus.groovy.ast.Parameter;
import org.codehaus.groovy.ast.expr.Expression;
import org.codehaus.groovy.ast.stmt.BlockStatement;
import org.codehaus.groovy.transform.BuilderASTTransformation;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.apache.groovy.ast.tools.ClassNodeUtils.addGeneratedInnerClass;
import static org.apache.groovy.ast.tools.ClassNodeUtils.addGeneratedMethod;
import static org.codehaus.groovy.ast.ClassHelper.OBJECT_TYPE;
import static org.codehaus.groovy.ast.tools.GeneralUtils.args;
import static org.codehaus.groovy.ast.tools.GeneralUtils.assignX;
import static org.codehaus.groovy.ast.tools.GeneralUtils.block;
import static org.codehaus.groovy.ast.tools.GeneralUtils.callX;
import static org.codehaus.groovy.ast.tools.GeneralUtils.constX;
import static org.codehaus.groovy.ast.tools.GeneralUtils.ctorX;
import static org.codehaus.groovy.ast.tools.GeneralUtils.declS;
import static org.codehaus.groovy.ast.tools.GeneralUtils.localVarX;
import static org.codehaus.groovy.ast.tools.GeneralUtils.param;
import static org.codehaus.groovy.ast.tools.GeneralUtils.params;
import static org.codehaus.groovy.ast.tools.GeneralUtils.propX;
import static org.codehaus.groovy.ast.tools.GeneralUtils.returnS;
import static org.codehaus.groovy.ast.tools.GeneralUtils.stmt;
import static org.codehaus.groovy.ast.tools.GeneralUtils.varX;
import static org.codehaus.groovy.ast.tools.GenericsUtils.correctToGenericsSpecRecurse;
import static org.codehaus.groovy.ast.tools.GenericsUtils.createGenericsSpec;
import static org.codehaus.groovy.ast.tools.GenericsUtils.extractSuperClassGenerics;
import static org.codehaus.groovy.ast.tools.GenericsUtils.newClass;
import static org.codehaus.groovy.transform.AbstractASTTransformation.getMemberStringValue;
import static org.codehaus.groovy.transform.BuilderASTTransformation.NO_EXCEPTIONS;
import static org.codehaus.groovy.transform.BuilderASTTransformation.NO_PARAMS;
import static org.objectweb.asm.Opcodes.ACC_PRIVATE;
import static org.objectweb.asm.Opcodes.ACC_PUBLIC;
import static org.objectweb.asm.Opcodes.ACC_STATIC;

/**
 * This strategy is used with the {@link Builder} AST transform to create a builder helper class
 * for the fluent creation of instances of a specified class.&nbsp;It can be used at the class,
 * static method or constructor levels.
 *
 * You use it as follows:
 * <pre class="groovyTestCase">
 * import groovy.transform.builder.*
 *
 * {@code @Builder}
 * class Person {
 *     String firstName
 *     String lastName
 *     int age
 * }
 * def person = Person.builder().firstName("Robert").lastName("Lewandowski").age(21).build()
 * assert person.firstName == "Robert"
 * assert person.lastName == "Lewandowski"
 * assert person.age == 21
 * </pre>
 * The {@code prefix} annotation attribute can be used to create setters with a different naming convention. The default is the
 * empty string but you could change that to "set" as follows:
 * <pre class="groovyTestCase">
 * {@code @groovy.transform.builder.Builder}(prefix='set')
 * class Person {
 *     String firstName
 *     String lastName
 *     int age
 * }
 * def p2 = Person.builder().setFirstName("Robert").setLastName("Lewandowski").setAge(21).build()
 * </pre>
 * or using a prefix of 'with' would result in usage like this:
 * <pre>
 * def p3 = Person.builder().withFirstName("Robert").withLastName("Lewandowski").withAge(21).build()
 * </pre>
 *
 * You can also use the {@code @Builder} annotation in combination with this strategy on one or more constructor or
 * static method instead of or in addition to using it at the class level. An example with a constructor follows:
 * <pre class="groovyTestCase">
 * import groovy.transform.ToString
 * import groovy.transform.builder.Builder
 *
 * {@code @ToString}
 * class Person {
 *     String first, last
 *     int born
 *
 *     {@code @Builder}
 *     Person(String roleName) {
 *         if (roleName == 'Jack Sparrow') {
 *             first = 'Johnny'; last = 'Depp'; born = 1963
 *         }
 *     }
 * }
 * assert Person.builder().roleName("Jack Sparrow").build().toString() == 'Person(Johnny, Depp, 1963)'
 * </pre>
 * In this case, the parameter(s) for the constructor or static method become the properties available
 * in the builder. For the case of a static method, the return type of the static method becomes the
 * class of the instance being created. For static factory methods, this is normally the class containing the
 * static method but in general it can be any class.
 *
 * Note: if using more than one {@code @Builder} annotation, which is only possible when using static method
 * or constructor variants, it is up to you to ensure that any generated helper classes or builder methods
 * have unique names. E.g.&nbsp;we can modify the previous example to have three builders. At least two of the builders
 * in our case will need to set the 'builderClassName' and 'builderMethodName' annotation attributes to ensure
 * we have unique names. This is shown in the following example:
 * <pre class="groovyTestCase">
 * import groovy.transform.builder.*
 * import groovy.transform.*
 *
 * {@code @ToString}
 * {@code @Builder}
 * class Person {
 *     String first, last
 *     int born
 *
 *     Person(){} // required to retain no-arg constructor
 *
 *     {@code @Builder}(builderClassName='MovieBuilder', builderMethodName='byRoleBuilder')
 *     Person(String roleName) {
 *         if (roleName == 'Jack Sparrow') {
 *             this.first = 'Johnny'; this.last = 'Depp'; this.born = 1963
 *         }
 *     }
 *
 *     {@code @Builder}(builderClassName='SplitBuilder', builderMethodName='splitBuilder')
 *     static Person split(String name, int year) {
 *         def parts = name.split(' ')
 *         new Person(first: parts[0], last: parts[1], born: year)
 *     }
 * }
 *
 * assert Person.splitBuilder().name("Johnny Depp").year(1963).build().toString() == 'Person(Johnny, Depp, 1963)'
 * assert Person.byRoleBuilder().roleName("Jack Sparrow").build().toString() == 'Person(Johnny, Depp, 1963)'
 * assert Person.builder().first("Johnny").last('Depp').born(1963).build().toString() == 'Person(Johnny, Depp, 1963)'
 * </pre>
 *
 * The 'forClass' annotation attribute for the {@code @Builder} transform isn't applicable for this strategy.
 * The 'useSetters' annotation attribute for the {@code @Builder} transform is ignored by this strategy which always uses setters.
 */
public class DefaultStrategy extends BuilderASTTransformation.AbstractBuilderStrategy {
    private static final Expression DEFAULT_INITIAL_VALUE = null;
    private static final int PUBLIC_STATIC = ACC_PUBLIC | ACC_STATIC;

    public void build(BuilderASTTransformation transform, AnnotatedNode annotatedNode, AnnotationNode anno) {
        if (unsupportedAttribute(transform, anno, "forClass")) return;
        if (unsupportedAttribute(transform, anno, "force")) return;
        if (annotatedNode instanceof ClassNode) {
            buildClass(transform, (ClassNode) annotatedNode, anno);
        } else if (annotatedNode instanceof MethodNode) {
            buildMethod(transform, (MethodNode) annotatedNode, anno);
        }
    }

    public void buildMethod(BuilderASTTransformation transform, MethodNode mNode, AnnotationNode anno) {
        if (transform.getMemberValue(anno, "includes") != null || transform.getMemberValue(anno, "excludes") != null) {
            transform.addError("Error during " + BuilderASTTransformation.MY_TYPE_NAME +
                    " processing: includes/excludes only allowed on classes", anno);
        }
        ClassNode buildee = mNode.getDeclaringClass();
        ClassNode builder = createBuilder(anno, buildee);
        createBuilderFactoryMethod(anno, buildee, builder);
        for (Parameter parameter : mNode.getParameters()) {
            builder.addField(createFieldCopy(buildee, parameter));
            addGeneratedMethod(builder, createBuilderMethodForProp(builder, new PropertyInfo(parameter.getName(), parameter.getType()), getPrefix(anno)));
        }
        addGeneratedMethod(builder, createBuildMethodForMethod(anno, buildee, mNode, mNode.getParameters()));
    }

    public void buildClass(BuilderASTTransformation transform, ClassNode buildee, AnnotationNode anno) {
        List<String> excludes = new ArrayList<String>();
        List<String> includes = new ArrayList<String>();
        includes.add(Undefined.STRING);
        if (!getIncludeExclude(transform, anno, buildee, excludes, includes)) return;
        if (includes.size() == 1 && Undefined.isUndefined(includes.get(0))) includes = null;
        ClassNode builder = createBuilder(anno, buildee);
        createBuilderFactoryMethod(anno, buildee, builder);
//        List<FieldNode> fields = getFields(transform, anno, buildee);
        boolean allNames = transform.memberHasValue(anno, "allNames", true);
        boolean allProperties = !transform.memberHasValue(anno, "allProperties", false);
        List<PropertyInfo> props = getPropertyInfos(transform, anno, buildee, excludes, includes, allNames, allProperties);
        for (PropertyInfo pi : props) {
            ClassNode correctedType = getCorrectedType(buildee, pi.getType(), builder);
            String fieldName = pi.getName();
            builder.addField(createFieldCopy(buildee, fieldName, correctedType));
            addGeneratedMethod(builder, createBuilderMethodForProp(builder, new PropertyInfo(fieldName, correctedType), getPrefix(anno)));
        }
        addGeneratedMethod(builder, createBuildMethod(anno, buildee, props));
    }

    private static ClassNode getCorrectedType(ClassNode buildee, ClassNode fieldType, ClassNode declaringClass) {
        Map<String, ClassNode> genericsSpec = createGenericsSpec(declaringClass);
        extractSuperClassGenerics(fieldType, buildee, genericsSpec);
        return correctToGenericsSpecRecurse(genericsSpec, fieldType);
    }

    private static void createBuilderFactoryMethod(AnnotationNode anno, ClassNode buildee, ClassNode builder) {
        addGeneratedInnerClass(buildee, builder);
        addGeneratedMethod(buildee, createBuilderMethod(anno, builder));
    }

    private static ClassNode createBuilder(AnnotationNode anno, ClassNode buildee) {
        return new InnerClassNode(buildee, getFullName(anno, buildee), PUBLIC_STATIC, OBJECT_TYPE);
    }

    private static String getFullName(AnnotationNode anno, ClassNode buildee) {
        String builderClassName = getMemberStringValue(anno, "builderClassName", buildee.getNameWithoutPackage() + "Builder");
        return buildee.getName() + "$" + builderClassName;
    }

    private static String getPrefix(AnnotationNode anno) {
        return getMemberStringValue(anno, "prefix", "");
    }

    private static MethodNode createBuildMethodForMethod(AnnotationNode anno, ClassNode buildee, MethodNode mNode, Parameter[] params) {
        String buildMethodName = getMemberStringValue(anno, "buildMethodName", "build");
        final BlockStatement body = new BlockStatement();
        ClassNode returnType;
        if (mNode instanceof ConstructorNode) {
            returnType = newClass(buildee);
            body.addStatement(returnS(ctorX(newClass(mNode.getDeclaringClass()), args(params))));
        } else {
            body.addStatement(returnS(callX(newClass(mNode.getDeclaringClass()), mNode.getName(), args(params))));
            returnType = newClass(mNode.getReturnType());
        }
        return new MethodNode(buildMethodName, ACC_PUBLIC, returnType, NO_PARAMS, NO_EXCEPTIONS, body);
    }

    private static MethodNode createBuilderMethod(AnnotationNode anno, ClassNode builder) {
        String builderMethodName = getMemberStringValue(anno, "builderMethodName", "builder");
        final BlockStatement body = new BlockStatement();
        body.addStatement(returnS(ctorX(builder)));
        return new MethodNode(builderMethodName, PUBLIC_STATIC, builder, NO_PARAMS, NO_EXCEPTIONS, body);
    }

    private static MethodNode createBuildMethod(AnnotationNode anno, ClassNode buildee, List<PropertyInfo> props) {
        String buildMethodName = getMemberStringValue(anno, "buildMethodName", "build");
        final BlockStatement body = new BlockStatement();
        body.addStatement(returnS(initializeInstance(buildee, props, body)));
        return new MethodNode(buildMethodName, ACC_PUBLIC, newClass(buildee), NO_PARAMS, NO_EXCEPTIONS, body);
    }

    private MethodNode createBuilderMethodForProp(ClassNode builder, PropertyInfo pinfo, String prefix) {
        ClassNode fieldType = pinfo.getType();
        String fieldName = pinfo.getName();
        String setterName = getSetterName(prefix, fieldName);
        return new MethodNode(setterName, ACC_PUBLIC, newClass(builder), params(param(fieldType, fieldName)), NO_EXCEPTIONS, block(
                stmt(assignX(propX(varX("this"), constX(fieldName)), varX(fieldName, fieldType))),
                returnS(varX("this", builder))
        ));
    }

    private static FieldNode createFieldCopy(ClassNode buildee, Parameter param) {
        Map<String, ClassNode> genericsSpec = createGenericsSpec(buildee);
        extractSuperClassGenerics(param.getType(), buildee, genericsSpec);
        ClassNode correctedParamType = correctToGenericsSpecRecurse(genericsSpec, param.getType());
        return new FieldNode(param.getName(), ACC_PRIVATE, correctedParamType, buildee, param.getInitialExpression());
    }

    private static FieldNode createFieldCopy(ClassNode buildee, String fieldName, ClassNode fieldType) {
        return new FieldNode(fieldName, ACC_PRIVATE, fieldType, buildee, DEFAULT_INITIAL_VALUE);
    }

    private static Expression initializeInstance(ClassNode buildee, List<PropertyInfo> props, BlockStatement body) {
        Expression instance = localVarX("_the" + buildee.getNameWithoutPackage(), buildee);
        body.addStatement(declS(instance, ctorX(buildee)));
        for (PropertyInfo pi : props) {
            body.addStatement(stmt(assignX(propX(instance, pi.getName()), varX(pi.getName(), pi.getType()))));
        }
        return instance;
    }
}
