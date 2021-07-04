package javax.realtime;

public final class TestPortal 
{
	public static class HighResolutionTimeStub extends HighResolutionTime 
	{
		public HighResolutionTimeStub(long millis, int nanos, Clock clock) {
			super(millis, nanos, clock);
		}
	}
}
