/**************************************************************************
 * File name  : Safelet.java
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

import javax.realtime.MemoryArea;
import javax.safetycritical.annotate.Level;
import javax.safetycritical.annotate.Phase;
import javax.safetycritical.annotate.SCJAllowed;
import javax.safetycritical.annotate.SCJRestricted;

/**
 * A safety-critical application consists of one or more missions, executed 
 * concurrently or in sequence. Every safety-critical application is 
 * represented by an implementation of <code>Safelet</code> which identifies 
 * the outer-most <code>MissionSequencer</code>.
 * This outer-most <code>MissionSequencer</code> takes responsibility for 
 * running the sequence of missions that comprise this safety-critical application.
 * 
 * @version 1.2; - December 2013
 * 
 * @author Anders P. Ravn, Aalborg University, 
 * <A HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 * Hans S&oslash;ndergaard, VIA University College, Denmark, 
 * <A HREF="mailto:hso@viauc.dk">hso@via.dk</A>
 */
@SuppressWarnings("unused")
@SCJAllowed(Level.SUPPORT) 
@SCJRestricted(Phase.INITIALIZE)
public interface Safelet<MissionType extends Mission> {
	/**
     * The infrastructure invokes <code>getSequencer</code> to obtain the 
     * <code>MissionSequencer</code> object that oversees execution of missions 
     * for this application. The returned sequencer must reside in immortal memory.
     * 
     * @return The <code>MissionSequencer</code> responsible for selecting
     *   the sequence of <code>Mission</code>s that represent this safety-critical 
     *   application.
     */
	@SCJAllowed(Level.SUPPORT) 
	@SCJRestricted(Phase.INITIALIZE)
	public MissionSequencer<MissionType> getSequencer();

    /**
     *  @return the amount of immortal memory that must be available for 
     *    allocations to be performed by this application.
     */
	@SCJAllowed(Level.SUPPORT)
	public long immortalMemorySize();

	@SCJAllowed(Level.SUPPORT)
	@SCJRestricted(Phase.INITIALIZE)
	public void initializeApplication();

}
