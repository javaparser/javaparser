# Manual

### Printing the CompilationUnit to System output
```java
public class CuPrinter {

    public static void main(String[] args) throws Exception {
        // creates an input stream for the file to be parsed
        FileInputStream in = new FileInputStream("test.java");

        // parse the file
        CompilationUnit cu = JavaParser.parse(in);

        // prints the resulting compilation unit to default system output
        System.out.println(cu.toString());
    }
}
```
### Visiting class methods
```java
public class MethodPrinter {

    public static void main(String[] args) throws Exception {
        // creates an input stream for the file to be parsed
        FileInputStream in = new FileInputStream("test.java");

        // parse it
        CompilationUnit cu = JavaParser.parse(in);

        // visit and print the methods names
        new MethodVisitor().visit(cu, null);
    }

    /**
     * Simple visitor implementation for visiting MethodDeclaration nodes.
     */
    private static class MethodVisitor extends VoidVisitorAdapter<Void> {
        @Override
        public void visit(MethodDeclaration n, Void arg) {
            /* here you can access the attributes of the method.
             this method will be called for all methods in this 
             CompilationUnit, including inner class methods */
            System.out.println(n.getName());
            super.visit(n, arg);
        }
    }
}
```
### Changing methods from a class with a visitor
```java
public class MethodChanger {

    public static void main(String[] args) throws Exception {
        // parse a file
        CompilationUnit cu = JavaParser.parse(new File("test.java"));

        // visit and change the methods names and parameters
        new MethodChangerVisitor().visit(cu, null);

        // prints the changed compilation unit
        System.out.println(cu);
    }

    /**
     * Simple visitor implementation for visiting MethodDeclaration nodes.
     */
    private static class MethodChangerVisitor extends VoidVisitorAdapter<Void> {
        @Override
        public void visit(MethodDeclaration n, Void arg) {
            // change the name of the method to upper case
            n.setName(n.getNameAsString().toUpperCase());

            // add a new parameter to the method
            n.addParameter("int", "value");
        }
    }
}
```
### Changing methods from a class without a visitor
```java
public class MethodChanger {

    public static void main(String[] args) throws Exception {
        // creates an input stream for the file to be parsed
        FileInputStream in = new FileInputStream("test.java");
        
        // parse the file
        CompilationUnit cu = JavaParser.parse(in);

        // change the methods names and parameters
        changeMethods(cu);

        // prints the changed compilation unit
        System.out.println(cu.toString());
    }

    private static void changeMethods(CompilationUnit cu) {
        // Go through all the types in the file
        NodeList<TypeDeclaration<?>> types = cu.getTypes();
        for (TypeDeclaration<?> type : types) {
            // Go through all fields, methods, etc. in this type
            NodeList<BodyDeclaration<?>> members = type.getMembers();
            for (BodyDeclaration<?> member : members) {
                if (member instanceof MethodDeclaration) {
                    MethodDeclaration method = (MethodDeclaration) member;
                    changeMethod(method);
                }
            }
        }
    }

    private static void changeMethod(MethodDeclaration n) {
        // change the name of the method to upper case
        n.setName(n.getNameAsString().toUpperCase());

        // create the new parameter
        n.addParameter(INT_TYPE, "value");
    }
}
```
### Creating a CompilationUnit from scratch
JavaParser has two main approaches for constructing nodes:
- Use the constructors of the node you want,
then use the setters if you need to change more,
then set or add your new node to an existing node.
- Take an existing node and use one of the builder methods on it.
 This is often a more efficient approach.
```java
public class ClassCreator {

    public static void main(String[] args) throws Exception {
        // creates the compilation unit
        CompilationUnit cu = createCU();

        // prints the created compilation unit
        System.out.println(cu.toString());
    }

    /**
     * creates the compilation unit
     */
    private static CompilationUnit createCU() {
        CompilationUnit cu = new CompilationUnit();
        // set the package
        cu.setPackage(new PackageDeclaration(Name.parse("java.parser.test")));

        // or a shortcut
        cu.setPackage("java.parser.test");

        // create the type declaration 
        ClassOrInterfaceDeclaration type = cu.addClass("GeneratedClass");

        // create a method
        EnumSet<Modifier> modifiers = EnumSet.of(Modifier.PUBLIC);
        MethodDeclaration method = new MethodDeclaration(modifiers, VOID_TYPE, "main");
        modifiers.add(Modifier.STATIC);
        method.setModifiers(modifiers);
        type.addMember(method);
        
        // or a shortcut
        MethodDeclaration main2 = type.addMethod("main2", Modifier.PUBLIC, Modifier.STATIC);

        // add a parameter to the method
        Parameter param = new Parameter(new ClassOrInterfaceType("String"), "args");
        param.setVarArgs(true);
        method.addParameter(param);
        
        // or a shortcut
        main2.addAndGetParameter(String.class, "args").setVarArgs(true);

        // add a body to the method
        BlockStmt block = new BlockStmt();
        method.setBody(block);

        // add a statement do the method body
        NameExpr clazz = new NameExpr("System");
        FieldAccessExpr field = new FieldAccessExpr(clazz, "out");
        MethodCallExpr call = new MethodCallExpr(field, "println");
        call.addArgument(new StringLiteralExpr("Hello World!"));
        block.addStatement(call);

        return cu;
    }
}
```
### Remove / Delete Node from AST
We're trying to delete a=20 from this class:
```java
public class D {
    public void foo(int e) {
        int a = 20;
    }
}
```
This can be done with a ModifierVisitorAdapter:
```java
class MyVisitor extends ModifierVisitorAdapter<Void> {
    @Override
    public Node visit(VariableDeclarator declarator, Void args) {
        if (declarator.getNameAsString().equals("a")
                // the initializer is optional, first check if there is one
                && declarator.getInitializer().isPresent()) {
            Expression expression = declarator.getInitializer().get();
            // We're looking for a literal integer.
            if (expression instanceof IntegerLiteralExpr) {
                // We found one. Is it literal integer 20?
                if (((IntegerLiteralExpr) expression).getValue().equals("20")) {
                    // Returning null means "remove this VariableDeclarator"
                    return null;
                }
            }
        }
        return declarator;
    }
}
```
In result you'll receive this:
```java
public class D {
    public void foo(int e) {
    }
}
```
