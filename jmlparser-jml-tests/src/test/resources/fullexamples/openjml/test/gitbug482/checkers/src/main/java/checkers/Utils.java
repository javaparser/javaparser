package checkers;
/**
 * Miscellaneous helper functions
 */
final class Utils
{
	/**
	 * works like `Math.signum(double)` but for ints
	 */
	public static int sign(int x)
	{
		
		if(x > 0)
			return 1;
		else if(x == 0)
			return 0;
		else
			return -1;
	}
}
