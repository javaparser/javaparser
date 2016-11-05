package a;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import org.junit.Test;

class X {
    static class Y{
        
    }
}

public class wofjiowejf {
    public void a(){
        a.X.Y a;
    }
    
    @Test
    public void wjefwioefj() {
        CompilationUnit parse = JavaParser.parse("public class wofjiowejf {\n" +
                "    public void a(){\n" +
                "        a.b.X.Y a;\n" +
                "    }}");

        System.out.println(parse);
    }
}

