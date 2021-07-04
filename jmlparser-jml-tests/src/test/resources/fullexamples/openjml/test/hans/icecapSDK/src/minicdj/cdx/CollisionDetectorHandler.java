/**
 *  This file is part of miniCDx benchmark of oSCJ.
 *
 *   miniCDx is free software: you can redistribute it and/or modify
 *   it under the terms of the GNU Lesser General Public License as published by
 *   the Free Software Foundation, either version 3 of the License, or
 *   (at your option) any later version.
 *
 *   miniCDx is distributed in the hope that it will be useful,
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *   GNU Lesser General Public License for more details.
 *
 *   You should have received a copy of the GNU Lesser General Public License
 *   along with miniCDx.  If not, see <http://www.gnu.org/licenses/>.
 *
 *
 *   Copyright 2009, 2010 
 *   @authors  Daniel Tang, Ales Plsek
 *
 *   See: http://sss.cs.purdue.edu/projects/oscj/
 */
package minicdj.cdx;

import icecaptools.IcecapCompileMe;

import javax.realtime.PriorityParameters;
import javax.safetycritical.Mission;
import javax.safetycritical.PeriodicEventHandler;
import javax.safetycritical.StorageParameters;
import javax.scj.util.Priorities;

import minicdj.cdx.unannotated.NanoClock;

/*@javax.safetycritical.annotate.Scope("cdx.Level0Safelet")*/
/*@javax.safetycritical.annotate.RunsIn("cdx.CollisionDetectorHandler")*/
public class CollisionDetectorHandler extends PeriodicEventHandler 
{
  
  Mission mission;
  
    private final TransientDetectorScopeEntry cd = 
        new TransientDetectorScopeEntry(new StateTable(), Constants.GOOD_VOXEL_SIZE);
    public final NoiseGenerator noiseGenerator = new NoiseGenerator();

    public boolean stop = false;

    public CollisionDetectorHandler(Mission mission) {

        // these very large limits are reported to work with stack traces... of
        // errors encountered...
        // most likely they are unnecessarily large
        //super(null, null, null, Constants.TRANSIENT_DETECTOR_SCOPE_SIZE);
        
        
        // PeriodicEventHandler(PriorityParameters priority, PeriodicParameters release, StorageParameters storage)
        //new StorageParameters(memSize, null)
        super(new PriorityParameters(Priorities.PR98), null, 
              new StorageParameters(Constants.TRANSIENT_DETECTOR_SCOPE_SIZE, null, 0,0,0) ); // HSO
        this.mission = mission; // added missSeq as parameter
    }

    @IcecapCompileMe
    public void runDetectorInScope(final TransientDetectorScopeEntry cd) {
        Benchmarker.set(14);

        final RawFrame f = minicdj.cdx.ImmortalEntry.frameBuffer.getFrame();
        if (f == null) {
            ImmortalEntry.frameNotReadyCount++;
            devices.Console.println("Frame not ready");
            Benchmarker.done(14);
            return;
        }

        int framesProcessed = minicdj.cdx.ImmortalEntry.framesProcessed;
        if ((framesProcessed + minicdj.cdx.ImmortalEntry.droppedFrames) == minicdj.cdx.Constants.MAX_FRAMES) {
            stop = true;
            Benchmarker.done(14);
            return;
        } // should not be needed, anyway

        final long heapFreeBefore = Runtime.getRuntime().freeMemory();
        final long timeBefore = NanoClock.now();

        noiseGenerator.generateNoiseIfEnabled();
        Benchmarker.set(Benchmarker.RAPITA_SETFRAME);
        cd.setFrame(f);
        Benchmarker.done(Benchmarker.RAPITA_SETFRAME);
        // actually runs the detection logic in the given scope
        cd.run();

        final long timeAfter = NanoClock.now();
        final long heapFreeAfter = Runtime.getRuntime().freeMemory();

        if (ImmortalEntry.recordedRuns < ImmortalEntry.maxDetectorRuns) {
            ImmortalEntry.timesBefore[ImmortalEntry.recordedRuns] = timeBefore;
            ImmortalEntry.timesAfter[ImmortalEntry.recordedRuns] = timeAfter;
            ImmortalEntry.heapFreeBefore[ImmortalEntry.recordedRuns] = heapFreeBefore;
            ImmortalEntry.heapFreeAfter[ImmortalEntry.recordedRuns] = heapFreeAfter;
            ImmortalEntry.recordedRuns++;
        }

        minicdj.cdx.ImmortalEntry.framesProcessed++;

        if ((minicdj.cdx.ImmortalEntry.framesProcessed + minicdj.cdx.ImmortalEntry.droppedFrames) == minicdj.cdx.Constants.MAX_FRAMES)
            stop = true;
        Benchmarker.done(14);
    }

    public void handleAsyncEvent() {
        try {
            if (!stop) {
                long now = NanoClock.now();
                ImmortalEntry.detectorReleaseTimes[ImmortalEntry.recordedDetectorReleaseTimes] = now;
                ImmortalEntry.detectorReportedMiss[ImmortalEntry.recordedDetectorReleaseTimes] = false;
                ImmortalEntry.recordedDetectorReleaseTimes++;

                runDetectorInScope(cd);
            } else {
                devices.Console.println("Terminating");
                //Mission.getCurrentMission().requestSequenceTermination();
                //mission.requestSequenceTermination();
                mission.getSequencer().requestSequenceTermination();
            }
        } catch (Throwable e) {
            devices.Console.println("CollisionDetectorHandler:Exception thrown by runDetectorInScope: "
                    + e.getMessage());
            e.printStackTrace();
        }
    }

    /* HSO
    //@Override
    public void cleanUp() {
        // TODO Auto-generated method stub
        
    }*/

    /* HSO
    //@Override
    public void register() {
        // TODO Auto-generated method stub
        
    }*/

    //@Override
    public StorageParameters getThreadConfigurationParameters() {
        // TODO Auto-generated method stub
        return null;
    }
}