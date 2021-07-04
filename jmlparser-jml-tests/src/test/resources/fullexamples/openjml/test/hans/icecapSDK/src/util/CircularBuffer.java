package util;

import java.io.IOException;

public class CircularBuffer {

    private byte buffer[];
    private short rdPtr;
    private short wrPtr;
    private boolean full;

    private static Exception exp;
    
    static
    {
    	 exp = null;
    }
    
    @SuppressWarnings("serial")
	private static class CircularBufferException extends IOException
    {
    	private String message;

		@Override
		public String getMessage() {
			return message;
		}
		
		public void setMessage(String message)
		{
			this.message = message;
		}
    }
    
    public CircularBuffer(short length) {
        buffer = new byte[length];
        rdPtr = 0;
        wrPtr = 0;
        full = false;
    }

    public synchronized byte read() throws IOException {
        if (!isEmpty()) {
            byte val = buffer[rdPtr++];
            full = false;
            if (rdPtr == buffer.length)
            {
                rdPtr = 0;
            }
            return val;
        } else {
            initializeException("Read from empty buffer");
        	throw (IOException)exp;
        }
    }

    private void initializeException(String string)  {
		if (exp == null)
		{
			exp = new CircularBufferException();
		}
		((CircularBufferException)exp).setMessage(string);
	}

	public synchronized boolean write(byte b) throws IOException {
        if (!full) {
            buffer[wrPtr++] = b;
            if (wrPtr == buffer.length) {
                wrPtr = 0;
            }
            if (wrPtr == rdPtr) {
                full = true;
            }
            return full;
        }
        else
        {
        	initializeException("Write to full buffer");
        	throw (IOException)exp;
        }
    }

    public synchronized boolean isFull() {
        return full;
    }

    public synchronized boolean isEmpty() {
        if (full) {
            return false;
        }
        return (rdPtr == wrPtr);
    }

    public synchronized boolean write(char c) throws IOException {
        return write((byte)c);
    }

    public synchronized int capacity() {
        return buffer.length;
    }
}
