package bufclient;

import bytebuf.ByteBuf;

public class ByteBufClient {
	/*@ public normal_behavior
	@   requires b != null;
	@   requires b.limit >= 1;
	@   ensures \result == b.contents[0];
	@*/
	public /*@ pure @*/ byte getOne(ByteBuf b) {
		return b.get(0);
	}
}
