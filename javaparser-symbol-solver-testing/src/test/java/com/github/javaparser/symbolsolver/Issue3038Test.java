package com.github.javaparser.symbolsolver;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithStatements;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import java.util.List;
import java.util.concurrent.TimeUnit;

/**
 * An issue when resolving some name when there are a series of many prior {@link NodeWithStatements}s.
 * Each queues up solving in the prior adjacent statement,
 * which means we queue up a factorial number of duplicate resolve calls.
 * <br>
 * This test verifies that parsing the given code below runs in an non-crazy amount of time <i>(Leeway for slow CI)</i>.
 * Without any fixes applied, this takes multiple hours to run.
 */
public class Issue3038Test extends AbstractResolutionTest {
	// In no way should this take more than 2.5 seconds
	// Realistically this should take much less.
	private static final long TIME_LIMIT_MS = 2500;

	@Test
	@Timeout(value = TIME_LIMIT_MS, unit = TimeUnit.MILLISECONDS)
	public void test3038() {
		String code = "public class Foo{\n" +
				"    public static void main(String[] args) {\n" +
				"        String s0   = \"hello\";\n" +
				"        String s1   = \"hello\";\n" +
				"        String s2   = \"hello\";\n" +
				"        String s3   = \"hello\";\n" +
				"        String s4   = \"hello\";\n" +
				"        String s5   = \"hello\";\n" +
				"        String s6   = \"hello\";\n" +
				"        String s7   = \"hello\";\n" +
				"        String s8   = \"hello\";\n" +
				"        String s9   = \"hello\";\n" +
				"        String s10  = \"hello\";\n" +
				"        String s11  = \"hello\";\n" +
				"        String s12  = \"hello\";\n" +
				"        String s13  = \"hello\";\n" +
				"        String s14  = \"hello\";\n" +
				"        String s15  = \"hello\";\n" +
				"        String s16  = \"hello\";\n" +
				"        String s17  = \"hello\";\n" +
				"        String s18  = \"hello\";\n" +
				"        String s19  = \"hello\";\n" +
				"        String s20  = \"hello\";\n" +
				"        String s21  = \"hello\";\n" +
				"        String s22  = \"hello\";\n" +
				"        String s23  = \"hello\";\n" +
				"        String s24  = \"hello\";\n" +
				"        String s25  = \"hello\";\n" +
				"        String s26  = \"hello\";\n" +
				"        String s27  = \"hello\";\n" +
				"        String s28  = \"hello\";\n" +
				"        String s29  = \"hello\";\n" +
				"        String s30  = \"hello\";\n" +
				"        String s31  = \"hello\";\n" +
				"        String s32  = \"hello\";\n" +
				"        String s33  = \"hello\";\n" +
				"        String s34  = \"hello\";\n" +
				"        String s35  = \"hello\";\n" +
				"        String s36  = \"hello\";\n" +
				"        String s37  = \"hello\";\n" +
				"        String s38  = \"hello\";\n" +
				"        String s39  = \"hello\";\n" +
				"        String s40  = \"hello\";\n" +
				"        String s41  = \"hello\";\n" +
				"        String s42  = \"hello\";\n" +
				"        String s43  = \"hello\";\n" +
				"        String s44  = \"hello\";\n" +
				"        String s45  = \"hello\";\n" +
				"        String s46  = \"hello\";\n" +
				"        String s47  = \"hello\";\n" +
				"        String s48  = \"hello\";\n" +
				"        String s49  = \"hello\";\n" +
				"        String s50  = \"hello\";\n" +
				"        String s51  = \"hello\";\n" +
				"        String s52  = \"hello\";\n" +
				"        String s53  = \"hello\";\n" +
				"        String s54  = \"hello\";\n" +
				"        String s55  = \"hello\";\n" +
				"        String s56  = \"hello\";\n" +
				"        String s57  = \"hello\";\n" +
				"        String s58  = \"hello\";\n" +
				"        String s59  = \"hello\";\n" +
				"        String s60  = \"hello\";\n" +
				"        String s61  = \"hello\";\n" +
				"        String s62  = \"hello\";\n" +
				"        String s63  = \"hello\";\n" +
				"        String s64  = \"hello\";\n" +
				"        String s65  = \"hello\";\n" +
				"        String s66  = \"hello\";\n" +
				"        String s67  = \"hello\";\n" +
				"        String s68  = \"hello\";\n" +
				"        String s69  = \"hello\";\n" +
				"        String s70  = \"hello\";\n" +
				"        String s71  = \"hello\";\n" +
				"        String s72  = \"hello\";\n" +
				"        String s73  = \"hello\";\n" +
				"        String s74  = \"hello\";\n" +
				"        String s75  = \"hello\";\n" +
				"        String s76  = \"hello\";\n" +
				"        String s77  = \"hello\";\n" +
				"        String s78  = \"hello\";\n" +
				"        String s79  = \"hello\";\n" +
				"        String s80  = \"hello\";\n" +
				"        String s81  = \"hello\";\n" +
				"        String s82  = \"hello\";\n" +
				"        String s83  = \"hello\";\n" +
				"        String s84  = \"hello\";\n" +
				"        String s85  = \"hello\";\n" +
				"        String s86  = \"hello\";\n" +
				"        String s87  = \"hello\";\n" +
				"        String s88  = \"hello\";\n" +
				"        String s89  = \"hello\";\n" +
				"        String s90  = \"hello\";\n" +
				"        String s91  = \"hello\";\n" +
				"        String s92  = \"hello\";\n" +
				"        String s93  = \"hello\";\n" +
				"        String s94  = \"hello\";\n" +
				"        String s95  = \"hello\";\n" +
				"        String s96  = \"hello\";\n" +
				"        String s97  = \"hello\";\n" +
				"        String s98  = \"hello\";\n" +
				"        String s99  = \"hello\";\n" +
				"        String s100 = \"hello\";\n" +
				"        new Thread(){\n" +
				"            @Override\n" +
				"            public void run() {\n" +
				"                Foo foo = Foo.getInstance();\n" +
				"            }\n" +
				"        }.run();\n" +
				"    }\n" +
				"    static Foo getInstance() {\n" +
				"        return new Foo();\n" +
				"    }\n" +
				"}";
		run(code);
	}

	@Test
	@Timeout(value = TIME_LIMIT_MS, unit = TimeUnit.MILLISECONDS)
	public void testAlt3038() {
		String code = "public class Foo{\n" +
				"    public static void main(String[] args) {\n" +
				"        String s0   = \"hello\";\n" +
				"        String s1   = \"hello\";\n" +
				"        String s2   = \"hello\";\n" +
				"        String s3   = \"hello\";\n" +
				"        String s4   = \"hello\";\n" +
				"        String s5   = \"hello\";\n" +
				"        String s6   = \"hello\";\n" +
				"        String s7   = \"hello\";\n" +
				"        String s8   = \"hello\";\n" +
				"        String s9   = \"hello\";\n" +
				"        String s10  = \"hello\";\n" +
				"        String s11  = \"hello\";\n" +
				"        String s12  = \"hello\";\n" +
				"        String s13  = \"hello\";\n" +
				"        String s14  = \"hello\";\n" +
				"        String s15  = \"hello\";\n" +
				"        String s16  = \"hello\";\n" +
				"        String s17  = \"hello\";\n" +
				"        String s18  = \"hello\";\n" +
				"        String s19  = \"hello\";\n" +
				"        String s20  = \"hello\";\n" +
				"        String s21  = \"hello\";\n" +
				"        String s22  = \"hello\";\n" +
				"        String s23  = \"hello\";\n" +
				"        String s24  = \"hello\";\n" +
				"        String s25  = \"hello\";\n" +
				"        String s26  = \"hello\";\n" +
				"        String s27  = \"hello\";\n" +
				"        String s28  = \"hello\";\n" +
				"        String s29  = \"hello\";\n" +
				"        String s30  = \"hello\";\n" +
				"        String s31  = \"hello\";\n" +
				"        String s32  = \"hello\";\n" +
				"        String s33  = \"hello\";\n" +
				"        String s34  = \"hello\";\n" +
				"        String s35  = \"hello\";\n" +
				"        String s36  = \"hello\";\n" +
				"        String s37  = \"hello\";\n" +
				"        String s38  = \"hello\";\n" +
				"        String s39  = \"hello\";\n" +
				"        String s40  = \"hello\";\n" +
				"        String s41  = \"hello\";\n" +
				"        String s42  = \"hello\";\n" +
				"        String s43  = \"hello\";\n" +
				"        String s44  = \"hello\";\n" +
				"        String s45  = \"hello\";\n" +
				"        String s46  = \"hello\";\n" +
				"        String s47  = \"hello\";\n" +
				"        String s48  = \"hello\";\n" +
				"        String s49  = \"hello\";\n" +
				"        String s50  = \"hello\";\n" +
				"        String s51  = \"hello\";\n" +
				"        String s52  = \"hello\";\n" +
				"        String s53  = \"hello\";\n" +
				"        String s54  = \"hello\";\n" +
				"        String s55  = \"hello\";\n" +
				"        String s56  = \"hello\";\n" +
				"        String s57  = \"hello\";\n" +
				"        String s58  = \"hello\";\n" +
				"        String s59  = \"hello\";\n" +
				"        String s60  = \"hello\";\n" +
				"        String s61  = \"hello\";\n" +
				"        String s62  = \"hello\";\n" +
				"        String s63  = \"hello\";\n" +
				"        String s64  = \"hello\";\n" +
				"        String s65  = \"hello\";\n" +
				"        String s66  = \"hello\";\n" +
				"        String s67  = \"hello\";\n" +
				"        String s68  = \"hello\";\n" +
				"        String s69  = \"hello\";\n" +
				"        String s70  = \"hello\";\n" +
				"        String s71  = \"hello\";\n" +
				"        String s72  = \"hello\";\n" +
				"        String s73  = \"hello\";\n" +
				"        String s74  = \"hello\";\n" +
				"        String s75  = \"hello\";\n" +
				"        String s76  = \"hello\";\n" +
				"        String s77  = \"hello\";\n" +
				"        String s78  = \"hello\";\n" +
				"        String s79  = \"hello\";\n" +
				"        String s80  = \"hello\";\n" +
				"        String s81  = \"hello\";\n" +
				"        String s82  = \"hello\";\n" +
				"        String s83  = \"hello\";\n" +
				"        String s84  = \"hello\";\n" +
				"        String s85  = \"hello\";\n" +
				"        String s86  = \"hello\";\n" +
				"        String s87  = \"hello\";\n" +
				"        String s88  = \"hello\";\n" +
				"        String s89  = \"hello\";\n" +
				"        String s90  = \"hello\";\n" +
				"        String s91  = \"hello\";\n" +
				"        String s92  = \"hello\";\n" +
				"        String s93  = \"hello\";\n" +
				"        String s94  = \"hello\";\n" +
				"        String s95  = \"hello\";\n" +
				"        String s96  = \"hello\";\n" +
				"        String s97  = \"hello\";\n" +
				"        String s98  = \"hello\";\n" +
				"        String s99  = \"hello\";\n" +
				"        String s100 = \"hello\";\n" +
				"        Foo foo = Foo.getInstance();\n" +
				"    }\n" +
				"    static Foo getInstance() {\n" +
				"        return new Foo();\n" +
				"    }\n" +
				"}";
		run(code);
	}

	private void run(String code) {
		ParserConfiguration config = new ParserConfiguration();
		config.setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver(false)));
		StaticJavaParser.setConfiguration(config);

		CompilationUnit cu = StaticJavaParser.parse(code);

		List<NameExpr> exprs = cu.findAll(NameExpr.class);
		for (NameExpr expr : exprs) {
			long start = System.currentTimeMillis();
			try {
				expr.resolve();
			} catch (UnsolvedSymbolException ex) {
				// this is expected since we have no way for the resolver to find "Foo"
			}
			long end = System.currentTimeMillis();
			System.out.printf("Call to resolve '%s' took %dms", expr.toString(), (end - start));
		}
	}
}
