package account;


public class Accounts {
	
	private Object[] frames;
	
	public Accounts (Object[] frames) throws IllegalArgumentException {
		if (frames == null)
			throw new IllegalArgumentException("frames is null");
		// frames != null:
//		if (frames != null) {
//			for (int i = 0; i < frames.length; i++) {
//				if (frames[i] == null)
//					throw new IllegalArgumentException("a frame element is null");
//			}
//		}

		this.frames = new Object[frames.length];
		for (int i = 0; i < frames.length; i++)
			this.frames[i] = frames[i];
	}

	public Object[] getFrames() {
		return frames;
	}
}
