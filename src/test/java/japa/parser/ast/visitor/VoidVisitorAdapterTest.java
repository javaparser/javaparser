package japa.parser.ast.visitor;

import japa.parser.ast.body.VariableDeclaratorId;
import japa.parser.ast.stmt.BlockStmt;
import japa.parser.ast.stmt.TryStmt;
import org.junit.Test;

import java.util.concurrent.atomic.AtomicReference;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.CoreMatchers.is;
import static org.hamcrest.CoreMatchers.nullValue;
import static org.hamcrest.CoreMatchers.equalTo;

public final class VoidVisitorAdapterTest extends VisitorAdapterTest {

    @Test
    public void visitsResourcesOfTryStmt() {
        final String resourceName = "closeable";
        TryStmt tryStmt = givenTryStmtWithResource(resourceName);

        VoidVisitorAdapter<AtomicReference<String>> objectUnderTest = new VoidVisitorAdapter<AtomicReference<String>>() {
            @Override
            public void visit(VariableDeclaratorId n, AtomicReference<String> arg) {
                String oldValue = arg.getAndSet(n.getName());
                assertThat("Should only find one variable declaration ID", oldValue, is(nullValue()));
            }
        };

        AtomicReference<String> atomicReference = new AtomicReference<String>();
        objectUnderTest.visit(tryStmt, atomicReference);

        assertThat("Should have visited the TryStmt's resources!", atomicReference.get(), is(equalTo(resourceName)));
    }

    @Test
    public void handlesNullResourcesOfTryStmtGracefully() {
        TryStmt tryStmt = new TryStmt(1, 1, 2, 80, null, new BlockStmt(), null, null);

        VoidVisitorAdapter<Void> objectUnderTest = new VoidVisitorAdapter<Void>() {
        };

        objectUnderTest.visit(tryStmt, null);
    }

}
