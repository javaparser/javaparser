package thread;

public class Semaphore {
	private byte permits;

	public Semaphore(byte permits) {
		this.permits = permits;
	}

	public void acquire() {
		while (true)
		{
			if (permits > 0)
			{
				permits--;
				return;
			}
		}
	}

	public void release() {
		permits++;
	}
}
