package japa.parser.ast.visitor;

import japa.parser.ast.body.VariableDeclaratorId;
import japa.parser.ast.stmt.BlockStmt;
import japa.parser.ast.stmt.TryStmt;
import org.junit.Test;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.CoreMatchers.is;
import static org.hamcrest.CoreMatchers.equalTo;

public final class GenericVisitorAdapterTest extends VisitorAdapterTest {

    @Test
    public void visitsResourcesOfTryStmt() {
        final String resourceName = "closeable";
        TryStmt tryStmt = givenTryStmtWithResource(resourceName);

        GenericVisitorAdapter<String, Void> objectUnderTest = new GenericVisitorAdapter<String, Void>() {
            @Override
            public String visit(VariableDeclaratorId n, Void arg) {
                return n.getName();
            }
        };

        String result = objectUnderTest.visit(tryStmt, null);

        assertThat("Should have visited the TryStmt's resources!", result, is(equalTo(resourceName)));
    }

    @Test
    public void handlesNullResourcesOfTryStmtGracefully() {
        TryStmt tryStmt = new TryStmt(1, 1, 2, 80, null, new BlockStmt(), null, null);

        GenericVisitorAdapter<Void, Void> objectUnderTest = new GenericVisitorAdapter<Void, Void>() {
        };

        objectUnderTest.visit(tryStmt, null);
    }

}
