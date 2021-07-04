package devices;

import icecaptools.IcecapCompileMe;

import java.security.PrivilegedAction;

import sun.security.action.GetPropertyAction;

public class AccessController {

	@SuppressWarnings("unchecked")
	@IcecapCompileMe
	public static <T> T doPrivileged(PrivilegedAction<T>  action)
	{
		if (action instanceof GetPropertyAction)
		{
			GetPropertyAction gpa = (GetPropertyAction) action;
			String prop = gpa.run();
			return (T) prop;
		}
		return (T) new Boolean(false);
	}	
}
