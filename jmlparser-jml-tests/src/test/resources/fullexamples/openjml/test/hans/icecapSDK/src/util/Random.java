package util;

public class Random {

	private int m_w;
	private int m_z;
	 
	public Random()
	{
		m_w = 42;
		m_z = 0xcafebabe;
	}
	
	public int getInt()
	{
	    m_z = 36969 * (m_z & 65535) + (m_z >> 16);
	    m_w = 18000 * (m_w & 65535) + (m_w >> 16);
	    return (m_z << 16) + m_w;  /* 32-bit result */
	}

	public byte getByte() {
		return (byte) (getInt() & 0xff);
	}

	public byte getNonNegativeByte() {
		byte b = getByte();
		if (b < 0)
		{
			b = (byte) -b;
		}
		if (b < 0)
		{
			b = 0;
		}
		return b;
	}
}
