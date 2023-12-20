----------------------------- MODULE home_spec -----------------------------

EXTENDS Integers
(* --algorithm SmartHomeSecurity
variables
    doorSensor = "closed",
    glassBreakSensor = "noBreakage",
    cameraStatus = "off",
    motionStatus = "noMotion",
    alarmState = "off",
    systemMode = "disarmed",
    userNotified = "noNotification";

fair process HomeOwner = "Owner"
begin
    Owner:
    while (TRUE) do
        if (systemMode = "disarmed") then
            systemMode := "armedStay";
        elsif (userNotified = "Notification") then
            systemMode := "disarmed";
        end if;
    end while;
end process;


fair process SystemMode \in {"armedStay", "armedAway", "disarmed"}
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

process Sensor = "Sensor"
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


fair process Camera = "Camera"
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

\* BEGIN TRANSLATION (chksum(pcal) = "137ba2eb" /\ chksum(tla) = "674f73d")
VARIABLES doorSensor, glassBreakSensor, cameraStatus, motionStatus, 
          alarmState, systemMode, userNotified, pc

vars == << doorSensor, glassBreakSensor, cameraStatus, motionStatus, 
           alarmState, systemMode, userNotified, pc >>

ProcSet == {"Owner"} \cup ({"armedStay", "armedAway", "disarmed"}) \cup {"Sensor"} \cup {"Camera"}

Init == (* Global variables *)
        /\ doorSensor = "closed"
        /\ glassBreakSensor = "noBreakage"
        /\ cameraStatus = "off"
        /\ motionStatus = "noMotion"
        /\ alarmState = "off"
        /\ systemMode = "disarmed"
        /\ userNotified = "noNotification"
        /\ pc = [self \in ProcSet |-> CASE self = "Owner" -> "Owner"
                                        [] self \in {"armedStay", "armedAway", "disarmed"} -> "ModeChange"
                                        [] self = "Sensor" -> "SensorTrigger"
                                        [] self = "Camera" -> "CameraOperation"]

Owner == /\ pc["Owner"] = "Owner"
         /\ IF (systemMode = "disarmed")
               THEN /\ systemMode' = "armedStay"
               ELSE /\ IF (userNotified = "Notification")
                          THEN /\ systemMode' = "disarmed"
                          ELSE /\ TRUE
                               /\ UNCHANGED systemMode
         /\ pc' = [pc EXCEPT !["Owner"] = "Owner"]
         /\ UNCHANGED << doorSensor, glassBreakSensor, cameraStatus, 
                         motionStatus, alarmState, userNotified >>

HomeOwner == Owner

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

SensorTrigger == /\ pc["Sensor"] = "SensorTrigger"
                 /\ \/ /\ doorSensor' = "opened"
                       /\ IF (systemMode /= "disarmed")
                             THEN /\ alarmState' = "sounding"
                                  /\ userNotified' = "notificationSent"
                             ELSE /\ TRUE
                                  /\ UNCHANGED << alarmState, userNotified >>
                       /\ UNCHANGED glassBreakSensor
                    \/ /\ glassBreakSensor' = "breakageDetected"
                       /\ IF (systemMode /= "disarmed")
                             THEN /\ alarmState' = "sounding"
                                  /\ userNotified' = "notificationSent"
                             ELSE /\ TRUE
                                  /\ UNCHANGED << alarmState, userNotified >>
                       /\ UNCHANGED doorSensor
                    \/ /\ TRUE
                       /\ UNCHANGED <<doorSensor, glassBreakSensor, alarmState, userNotified>>
                 /\ pc' = [pc EXCEPT !["Sensor"] = "SensorTrigger"]
                 /\ UNCHANGED << cameraStatus, motionStatus, systemMode >>

Sensor == SensorTrigger

CameraOperation == /\ pc["Camera"] = "CameraOperation"
                   /\ IF (alarmState = "sounding")
                         THEN /\ cameraStatus' = "recording"
                         ELSE /\ cameraStatus' = "notRecording"
                   /\ pc' = [pc EXCEPT !["Camera"] = "CameraOperation"]
                   /\ UNCHANGED << doorSensor, glassBreakSensor, motionStatus, 
                                   alarmState, systemMode, userNotified >>

Camera == CameraOperation

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == HomeOwner \/ Sensor \/ Camera
           \/ (\E self \in {"armedStay", "armedAway", "disarmed"}: SystemMode(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(HomeOwner)
        /\ \A self \in {"armedStay", "armedAway", "disarmed"} : WF_vars(SystemMode(self))
        /\ WF_vars(Camera)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Wed Dec 20 14:23:27 MSK 2023 by dadro
\* Created Wed Dec 18 12:23:24 MSK 2023 by dadro