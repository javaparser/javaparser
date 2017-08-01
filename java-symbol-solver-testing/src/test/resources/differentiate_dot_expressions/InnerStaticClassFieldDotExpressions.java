import com.packageName.InnerStaticClassFieldContainer;

public class InnerStaticClassFieldDotExpressions {
    public static void main(String[] args) {
        // force the solving of the argument
        Integer.parseInt(InnerStaticClassFieldContainer.InnerClass.InnerInnerClass.MY_INT);
    }
}
