public class MyObject {
	
	private static final int ARRAY_SIZE = 10;
	private final MyFieldObject[] values = new MyFieldObject[ARRAY_SIZE];
	private final MyFieldObject value = new MyFieldObject();
	
	public MyObject() {
		for (int i = 0; i < ARRAY_SIZE; i++) {
			values[i] = new MyFieldObject();
		}
	}

	/*@ private normal_behavior
	  @ 	assignable values[*].x;
	  @*/
	public void assignInFieldInArrayElement() {
		for (int i = 0; i < ARRAY_SIZE; i++) {
			values[i].setX(i);
		}
	}
	
	/*@
	  @ private normal_behavior
	  @ 	assignable value.*;
	  @*/
	public void assignInField() {
		value.setX(1337);
		value.setY(3141592);
	}
	
	//OpenJML gives an error :(
	/*@
	  @ private normal_behavior
	  @ 	assignable values[*].*;
	  @*/
	public void assignToAllFieldsInArrayElements() {
		for (int i = 0; i < ARRAY_SIZE; i++) {
			values[i].setX(-i);
			values[ARRAY_SIZE-1-i].setY(i);
		}
	}
	
	
	private static final class MyFieldObject {
		
		private int x, y;
		
		public int getX() {
			return x;
		}
		
		public int getY() {
			return y;
		}
		
		public void setX(int x) {
			this.x = x;
		}
		
		public void setY(int y) {
			this.y = y;
		}
	}

}