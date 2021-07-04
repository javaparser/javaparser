/**************************************************************************
 * File name  : AsyncEventHandler.java
 * 
 * This file is part a SCJ Level 0 and Level 1 implementation, 
 * based on SCJ Draft, Version 0.94 25 June 2013.
 *
 * It is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as  
 * published by the Free Software Foundation, either version 3 of the 
 * License, or (at your option) any later version.
 *
 * This SCJ Level 0 and Level 1 implementation is distributed in the hope 
 * that it will be useful, but WITHOUT ANY WARRANTY; without even the  
 * implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  
 * See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this SCJ Level 0 and Level 1 implementation.  
 * If not, see <http://www.gnu.org/licenses/>.
 *
 * Copyright 2012 
 * @authors  Anders P. Ravn, Aalborg University, DK
 *           Stephan E. Korsholm and Hans S&oslash;ndergaard, 
 *             VIA University College, DK
 *************************************************************************/
package javax.realtime;

import javax.safetycritical.annotate.SCJAllowed;

/**
 * In SCJ, all asynchronous events must have their handlers bound to a 
 * thread when they are created (during the initialization phase). 
 * The binding is permanent. Thus, the <code>AsyncEventHandler</code> 
 * constructors are hidden from public view in the SCJ specification.
 * 
 *  @version 1.2; - December 2013
 * 
 * @author Anders P. Ravn, Aalborg University, 
 * <A HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 * Hans S&oslash;ndergaard, VIA University College, Denmark, 
 * <A HREF="mailto:hso@viauc.dk">hso@via.dk</A>
 */
@SCJAllowed(javax.safetycritical.annotate.Level.LEVEL_0)
public class AsyncEventHandler extends AbstractAsyncEventHandler {

	
	public void run() {
		handleAsyncEvent();
	}
	
	/**
	 * This method must be overridden by the application to provide the handling code.
	 */
	@SCJAllowed(javax.safetycritical.annotate.Level.SUPPORT)
	public void handleAsyncEvent() {
	}

}
