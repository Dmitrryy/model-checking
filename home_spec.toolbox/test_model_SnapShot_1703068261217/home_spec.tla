----------------------------- MODULE home_spec -----------------------------

(* --algorithm SmartHomeSecurity
variables
    doorSensor = "closed",
    glassBreakSensor = "noBreakage",
    cameraStatus = "off",
    motionStatus = "noMotion",
    alarmState = "off",
    systemMode = "disarmed",
    userNotified = "noNotification";

process SystemMode \in {"armedStay", "armedAway", "disarmed"}
begin
    ModeChange:
    while (TRUE) do
        with newMode \in {"armedStay", "armedAway", "disarmed"} do
            systemMode := newMode;
            if (systemMode = "disarmed") then
                alarmState := "off";
                cameraStatus := "off";
                userNotified := "noNotification";
            else
                cameraStatus := "on";
            end if;
        end with;
    end while;
end process;

\*process Sensor \in {1}
\*begin
\*    SensorTrigger:
\*    while (TRUE) do
\*        either
\*            doorSensor := "opened";
\*            if (systemMode /= "disarmed") then
\*                alarmState := "sounding";
\*                userNotified := "notificationSent";
\*            end if;
\*        or
\*            glassBreakSensor := "breakageDetected";
\*            if (systemMode /= "disarmed") then
\*                alarmState := "sounding";
\*                userNotified := "notificationSent";
\*            end if;
\*        or
\*            skip;
\*        end either;
\*    end while;
\*end process;
\*
\*process Camera \in {1}
\*begin
\*    CameraOperation:
\*    while (TRUE) do
\*        if (alarmState = "sounding") then
\*            cameraStatus := "recording";
\*        else
\*            cameraStatus := "notRecording";
\*        end if;
\*    end while;
\*end process;

end algorithm
*)

\* BEGIN TRANSLATION (chksum(pcal) = "c750b239" /\ chksum(tla) = "fbc4c85")
VARIABLES doorSensor, glassBreakSensor, cameraStatus, motionStatus, 
          alarmState, systemMode, userNotified, pc

vars == << doorSensor, glassBreakSensor, cameraStatus, motionStatus, 
           alarmState, systemMode, userNotified, pc >>

ProcSet == ({"armedStay", "armedAway", "disarmed"})

Init == (* Global variables *)
        /\ doorSensor = "closed"
        /\ glassBreakSensor = "noBreakage"
        /\ cameraStatus = "off"
        /\ motionStatus = "noMotion"
        /\ alarmState = "off"
        /\ systemMode = "disarmed"
        /\ userNotified = "noNotification"
        /\ pc = [self \in ProcSet |-> "ModeChange"]

ModeChange(self) == /\ pc[self] = "ModeChange"
                    /\ \E newMode \in {"armedStay", "armedAway", "disarmed"}:
                         /\ systemMode' = newMode
                         /\ IF (systemMode' = "disarmed")
                               THEN /\ alarmState' = "off"
                                    /\ cameraStatus' = "off"
                                    /\ userNotified' = "noNotification"
                               ELSE /\ cameraStatus' = "on"
                                    /\ UNCHANGED << alarmState, userNotified >>
                    /\ pc' = [pc EXCEPT ![self] = "ModeChange"]
                    /\ UNCHANGED << doorSensor, glassBreakSensor, motionStatus >>

SystemMode(self) == ModeChange(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in {"armedStay", "armedAway", "disarmed"}: SystemMode(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Wed Dec 20 13:30:53 MSK 2023 by dadro
\* Created Wed Dec 18 12:23:24 MSK 2023 by dadro
