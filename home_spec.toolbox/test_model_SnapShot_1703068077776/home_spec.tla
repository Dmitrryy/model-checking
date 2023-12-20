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

process Sensor \in {1}
begin
    SensorTrigger:
    while (TRUE) do
        either
            doorSensor := "opened";
            if (systemMode /= "disarmed") then
                alarmState := "sounding";
                userNotified := "notificationSent";
            end if;
        or
            glassBreakSensor := "breakageDetected";
            if (systemMode /= "disarmed") then
                alarmState := "sounding";
                userNotified := "notificationSent";
            end if;
        or
            skip;
        end either;
    end while;
end process;

process Camera \in {1}
begin
    CameraOperation:
    while (TRUE) do
        if (alarmState = "sounding") then
            cameraStatus := "recording";
        else
            cameraStatus := "notRecording";
        end if;
    end while;
end process;

end algorithm
*)

\* BEGIN TRANSLATION (chksum(pcal) = "ca803074" /\ chksum(tla) = "79f0fa94")
VARIABLES doorSensor, glassBreakSensor, cameraStatus, motionStatus, 
          alarmState, systemMode, userNotified, pc

vars == << doorSensor, glassBreakSensor, cameraStatus, motionStatus, 
           alarmState, systemMode, userNotified, pc >>

ProcSet == ({"armedStay", "armedAway", "disarmed"}) \cup ({1}) \cup ({1})

Init == (* Global variables *)
        /\ doorSensor = "closed"
        /\ glassBreakSensor = "noBreakage"
        /\ cameraStatus = "off"
        /\ motionStatus = "noMotion"
        /\ alarmState = "off"
        /\ systemMode = "disarmed"
        /\ userNotified = "noNotification"
        /\ pc = [self \in ProcSet |-> CASE self \in {"armedStay", "armedAway", "disarmed"} -> "ModeChange"
                                        [] self \in {1} -> "SensorTrigger"
                                        [] self \in {1} -> "CameraOperation"]

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

SensorTrigger(self) == /\ pc[self] = "SensorTrigger"
                       /\ \/ /\ doorSensor' = "opened"
                             /\ IF (systemMode /= "disarmed")
                                   THEN /\ alarmState' = "sounding"
                                        /\ userNotified' = "notificationSent"
                                   ELSE /\ TRUE
                                        /\ UNCHANGED << alarmState, 
                                                        userNotified >>
                             /\ UNCHANGED glassBreakSensor
                          \/ /\ glassBreakSensor' = "breakageDetected"
                             /\ IF (systemMode /= "disarmed")
                                   THEN /\ alarmState' = "sounding"
                                        /\ userNotified' = "notificationSent"
                                   ELSE /\ TRUE
                                        /\ UNCHANGED << alarmState, 
                                                        userNotified >>
                             /\ UNCHANGED doorSensor
                          \/ /\ TRUE
                             /\ UNCHANGED <<doorSensor, glassBreakSensor, alarmState, userNotified>>
                       /\ pc' = [pc EXCEPT ![self] = "SensorTrigger"]
                       /\ UNCHANGED << cameraStatus, motionStatus, systemMode >>

Sensor(self) == SensorTrigger(self)

CameraOperation(self) == /\ pc[self] = "CameraOperation"
                         /\ IF (alarmState = "sounding")
                               THEN /\ cameraStatus' = "recording"
                               ELSE /\ cameraStatus' = "notRecording"
                         /\ pc' = [pc EXCEPT ![self] = "CameraOperation"]
                         /\ UNCHANGED << doorSensor, glassBreakSensor, 
                                         motionStatus, alarmState, systemMode, 
                                         userNotified >>

Camera(self) == CameraOperation(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in {"armedStay", "armedAway", "disarmed"}: SystemMode(self))
           \/ (\E self \in {1}: Sensor(self))
           \/ (\E self \in {1}: Camera(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Wed Dec 20 13:27:21 MSK 2023 by dadro
\* Created Wed Dec 18 12:23:24 MSK 2023 by dadro
