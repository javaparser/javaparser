/**************************************************************************
 * File name  : PeriodicEventHandler.java
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

import javax.realtime.PeriodicParameters;
import javax.realtime.PriorityParameters;
import javax.safetycritical.annotate.SCJAllowed;

/**
 * This class permits the automatic periodic execution of code. 
 * The <code>handleAsyncEvent</code> method behaves as if the handler were 
 * attached to a periodic asynchronous event. <p>
 * 
 * This class is abstract, non-abstract sub-classes must implement the method
 * <code>handleAsyncEvent</code> and may override the default <code>cleanUp</code> method.
 * 
 * Note that the values in parameters passed to the constructors are those that will
 * be used by the infrastructure. Changing these values after construction will
 * have no impact on the created event handler.
 * 
 * @version 1.2; - December 2013
 * 
 * @author Anders P. Ravn, Aalborg University, <A
 *         HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 *         Hans S&oslash;ndergaard, VIA University College, Denmark, <A
 *         HREF="mailto:hso@viauc.dk">hso@via.dk</A>
 * 
 * @scjComment 
 *   - SCJ issue: One constructor only. <br>
 *   - SCJ issue: SCJ Draft says: constructor: param storage -> It must not be <code>null</code>. <br>
 *       An <code>IllegalArgumentException</code> is thrown if storage is null.
 *       But <code>ManagedEventHandler</code> does not require an 
 *       <code>IllegalArgumentException</code> thrown if storage is null.
 *       It only specifies: a non-null maximum storage. This can be satisfied by implementing:
 *       if storage parameter is null, a default value is given. <br>
 */
@SCJAllowed
public abstract class PeriodicEventHandler extends ManagedEventHandler {
	/** 
	 * Constructs a periodic event handler.
	 * 
	 * @param priority specifies the priority parameters for this periodic event handler. 
	 *   Must not be <code>null</code>.
	 * 
	 * @param release specifies the periodic release parameters, in particular the start time,
	 * period and deadline miss handler. Note that a relative start time is not relative to now,
	 * rather it is relative to the point in time when initialization is finished and the timers
	 * are started. This argument must not be <code>null</code>.
	 * 
	 * @param storage specifies the storage parameters for the periodic event handler. 
	 *   It must not be <code>null</code>.
	 * 
	 * @throws IllegalArgumentException if priority, release or storage is null.
	 */
	/*@ 
	  public normal_behavior
	    requires priority != null && release  != null;
	    ensures true; 
	  also
	  public exceptional_behavior
	    requires priority == null;
	    signals (IllegalArgumentException) true;
	  also
	  public exceptional_behavior
	    requires release == null;
	    signals (IllegalArgumentException) true;         
	@*/
	public PeriodicEventHandler(PriorityParameters priority,
			PeriodicParameters release, StorageParameters storage) {
		super(priority, release, storage);
	}

	public final void register() {
		super.register();
	}
}
