package bdd.steps;

import japa.parser.JavaParser;
import japa.parser.ParseException;
import japa.parser.ast.CompilationUnit;
import japa.parser.ast.visitor.CloneVisitor;
import org.jbehave.core.annotations.Given;
import org.jbehave.core.annotations.When;

import java.io.ByteArrayInputStream;
import java.util.Map;

public class VisitorSteps {

    private Map<String, Object> state;

    public VisitorSteps(Map<String, Object> state){
        this.state = state;
    }

    @When("the CompilationUnit is cloned to the second CompilationUnit")
    public void whenTheSecondCompilationUnitIsCloned() {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        CompilationUnit compilationUnit2 = (CompilationUnit)compilationUnit.accept(new CloneVisitor(), null);
        state.put("cu2", compilationUnit2);
    }
}
