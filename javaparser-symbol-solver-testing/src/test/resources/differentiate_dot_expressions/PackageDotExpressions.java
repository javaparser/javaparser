public class PackageDotExpressions {
    public static void main(String[] args) {
        // Method call from package prefix
        com.packageName.ClassInPackage.staticMethod();

        // Static method calls inside inner classes with package prefix
        com.packageName.InnerClassContainer.InnerClass.methodCall();
        com.packageName.InnerClassContainer.InnerClass.InnerInnerClass.innerMethodCall();
        com.packageName.InnerClassContainer.InnerClass.InnerInnerClass.InnerInnerInnerClass.innerInnerMethodCall();

        // Method calls from field objects with package prefix
        com.packageName.InnerClassFieldContainer.outerField.containerField.containerField.firstContainerMethod();
        com.packageName.InnerClassFieldContainer.InnerClass.innerField.containerField.containerField.secondContainerMethod();
        com.packageName.InnerClassFieldContainer.InnerClass.InnerInnerClass.InnerInnerInnerClass.innerInnerInnerField.thirdContainerMethod();
    }
}
