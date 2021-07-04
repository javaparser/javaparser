/**************************************************************************
 * File name  : PrivateMemory.java
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
package javax.safetycritical;

import icecaptools.IcecapCompileMe;

import javax.realtime.MemoryArea;
import javax.safetycritical.annotate.Level;
import javax.safetycritical.annotate.SCJAllowed;

/**
 * This class cannot be directly instantiated by the application; 
 * hence there are no public constructors. Every <code>Schedulable</code> 
 * object is provided with one instance of <code>PrivateMemory</code> ,
 * its root private memory area. A schedulable object active within a private
 * memory area can create nested private memory areas through the 
 * <code>enterPrivateMemory</code> method of <code>ManagedMemory</code>. 
 * <p>
 * The rules for nested entering into a private memory are that the private memory area
 * must be the current allocation context, and the calling schedulable object has to be
 * the owner of the memory area. The owner of the memory area is defined to be the
 * schedulable object that it was provided for.
 *   
 * @version 1.2; - December 2013
 * 
 * @author Anders P. Ravn, Aalborg University, 
 * <A HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 * Hans S&oslash;ndergaard, VIA University College, Denmark, 
 * <A HREF="mailto:hso@viauc.dk">hso@via.dk</A>
 * 
 * @scjComment 
 *  SCJ issue: This class should not be public.
 */
@SCJAllowed(Level.INFRASTRUCTURE)
public final class PrivateMemory extends ManagedMemory // HSO: not public
{
	@IcecapCompileMe
	PrivateMemory(int size, int BackingStoreOfThisMemory, 
			      MemoryArea backingStoreProvider, String label) {
		super(size, BackingStoreOfThisMemory, backingStoreProvider, label);
	}

}
