package unitTest;

/**
 * Thrown when an assert equals for Strings failed.
 */
public class ComparisonFailure extends AssertionFailedError {
	private static final long serialVersionUID = 1L;

	private String fExpected;

	private String fActual;

	/**
	 * Constructs a comparison failure.
	 * 
	 * @param message
	 *            the identifying message or null
	 * @param expected
	 *            the expected string value
	 * @param actual
	 *            the actual string value
	 */
	public ComparisonFailure(String message, String expected, String actual) {
		super(message);
		fExpected = expected;
		fActual = actual;
	}

	/**
	 * Returns "..." in place of common prefix and "..." in place of common
	 * suffix between expected and actual.
	 * 
	 * @see java.lang.Throwable#getMessage()
	 */
	public String getMessage() {
		// return new ComparisonCompactor(MAX_CONTEXT_LENGTH, fExpected,
		// fActual)
		// .compact(super.getMessage());
		return super.getMessage();
	}

	/**
	 * Gets the actual string value
	 * 
	 * @return the actual string value
	 */
	public String getActual() {
		return fActual;
	}

	/**
	 * Gets the expected string value
	 * 
	 * @return the expected string value
	 */
	public String getExpected() {
		return fExpected;
	}
}