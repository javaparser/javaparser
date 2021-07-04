/**************************************************************************
 * File name: AperiodicEventHandler.java
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

import javax.realtime.AperiodicParameters;
import javax.realtime.PriorityParameters;
import javax.safetycritical.annotate.Level;
import javax.safetycritical.annotate.Phase;
import javax.safetycritical.annotate.SCJAllowed;
import javax.safetycritical.annotate.SCJRestricted;

/**
 * This class permits the explicit release of application code.
 * Concrete subclasses must implement the <code>handleAsyncEvent</code> method 
 * and may override the default <code>cleanUp</code> method. <br>
 * 
 * Note that the values in parameters passed to the constructors are those that will be used by the 
 * infrastructure. Changing these values after construction will have no impact on the created event handler.
 * 
 * @version 1.2; - December 2013
 * 
 * @author Anders P. Ravn, Aalborg University, 
 * <A HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 * Hans S&oslash;ndergaard, VIA University College, Denmark, 
 * <A HREF="mailto:hso@viauc.dk">hso@via.dk</A>
 */
@SCJAllowed(Level.LEVEL_1)
public abstract class AperiodicEventHandler extends ManagedEventHandler {
	/**
	  * The scheduler that releases the handler.
	*/
	private PriorityScheduler sch;

	/**
	 * Constructs an aperiodic event handler that can be explicitly released.
	 * 
	 * @param priority is the priority parameters for this aperiodic event handler; it must not be null.
	 * @param release is the release parameters for this aperiodic event handler; it must not be null.
	 * @param storage is the <code>StorageParameters</code> for this aperiodic event handler.
	 * 
	 * @throws <code>IllegalArgumentException</code> if <code>priority</code> or <code> release</code> is null.
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
	@SCJAllowed(Level.LEVEL_1)
	@SCJRestricted(Phase.INITIALIZE)
	public AperiodicEventHandler(PriorityParameters priority,
			AperiodicParameters release, StorageParameters storage) {
		super(priority, release, storage);
		if (priority == null || release == null)
			throw new IllegalArgumentException("null argument");
	}

	@SCJAllowed(Level.INFRASTRUCTURE)
	@SCJRestricted(Phase.INITIALIZE)
	public final void register() {
		super.register();
		sch = PriorityScheduler.instance();
	}

	/**
	 * Release this aperiodic event handler
	 */
	/*@ 
	  public behavior
	//      requires MissionSequencer.getPhase() == Phase.EXECUTE;
	    requires Mission.getMission().isRegistered(this);      
	  
	//      ensures MissionSequencer.getPhase() == Phase.EXECUTE;
	    ensures Mission.getMission().isRegistered(this);
	//      ensures PriorityScheduler.activated(this);      
	  @*/
	@SCJAllowed
	public final void release() {
		sch.release(this);
	}

}
