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
    
define
SAFEWindowBreakAlarm == (systemMode = "armedStay" \/ systemMode = "armedAway") /\ glassBreakSensor = "breakageDetected" => alarmState = "sounding"
SAFEDoorOpenAlarm == (systemMode = "armedStay" \/ systemMode = "armedAway") /\ doorSensor = "opened" => alarmState = "sounding"
SAFEMotionIgnored == (systemMode = "armedStay" \/ systemMode = "disabled") /\ (motionStatus = "Motion" /\ doorSensor /= "opened" /\ glassBreakSensor /= "breakageDetected") => alarmState /= "sounding"
end define;


fair process HomeOwner = "Owner"
begin
    Owner:
    while (TRUE) do
        if (systemMode = "disarmed") then
            doorSensor := "closed";
            glassBreakSensor := "noBreakage";
            cameraStatus := "off";
            motionStatus := "noMotion";
            alarmState := "off";
            userNotified := "noNotification";
            systemMode := "armedStay";
        elsif (userNotified = "notificationSent") then
            (* reset system *)
            systemMode := "disarmed";
            doorSensor := "closed";
            glassBreakSensor := "noBreakage";
            cameraStatus := "off";
            motionStatus := "noMotion";
            alarmState := "off";
            userNotified := "noNotification";
        elsif (systemMode = "armedStay") then
            (* go away from home *)
            systemMode := "armedAway";
        end if;
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
            motionStatus := "Motion";
            if (systemMode = "armedAway") then
                alarmState := "sounding";
                userNotified := "notificationSent";
            end if;
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

\* BEGIN TRANSLATION (chksum(pcal) = "31c877f3" /\ chksum(tla) = "2a637bd8")
VARIABLES doorSensor, glassBreakSensor, cameraStatus, motionStatus, 
          alarmState, systemMode, userNotified, pc

(* define statement *)
SAFEWindowBreakAlarm == (systemMode = "armedStay" \/ systemMode = "armedAway") /\ glassBreakSensor = "breakageDetected" => alarmState = "sounding"
SAFEDoorOpenAlarm == (systemMode = "armedStay" \/ systemMode = "armedAway") /\ doorSensor = "opened" => alarmState = "sounding"
SAFEMotionIgnored == (systemMode = "armedStay" \/ systemMode = "disabled") /\ (motionStatus = "Motion" /\ doorSensor /= "opened" /\ glassBreakSensor /= "breakageDetected") => alarmState /= "sounding"


vars == << doorSensor, glassBreakSensor, cameraStatus, motionStatus, 
           alarmState, systemMode, userNotified, pc >>

ProcSet == {"Owner"} \cup {"Sensor"} \cup {"Camera"}

Init == (* Global variables *)
        /\ doorSensor = "closed"
        /\ glassBreakSensor = "noBreakage"
        /\ cameraStatus = "off"
        /\ motionStatus = "noMotion"
        /\ alarmState = "off"
        /\ systemMode = "disarmed"
        /\ userNotified = "noNotification"
        /\ pc = [self \in ProcSet |-> CASE self = "Owner" -> "Owner"
                                        [] self = "Sensor" -> "SensorTrigger"
                                        [] self = "Camera" -> "CameraOperation"]

Owner == /\ pc["Owner"] = "Owner"
         /\ IF (systemMode = "disarmed")
               THEN /\ doorSensor' = "closed"
                    /\ glassBreakSensor' = "noBreakage"
                    /\ cameraStatus' = "off"
                    /\ motionStatus' = "noMotion"
                    /\ alarmState' = "off"
                    /\ userNotified' = "noNotification"
                    /\ systemMode' = "armedStay"
               ELSE /\ IF (userNotified = "notificationSent")
                          THEN /\ systemMode' = "disarmed"
                               /\ doorSensor' = "closed"
                               /\ glassBreakSensor' = "noBreakage"
                               /\ cameraStatus' = "off"
                               /\ motionStatus' = "noMotion"
                               /\ alarmState' = "off"
                               /\ userNotified' = "noNotification"
                          ELSE /\ IF (systemMode = "armedStay")
                                     THEN /\ systemMode' = "armedAway"
                                     ELSE /\ TRUE
                                          /\ UNCHANGED systemMode
                               /\ UNCHANGED << doorSensor, glassBreakSensor, 
                                               cameraStatus, motionStatus, 
                                               alarmState, userNotified >>
         /\ pc' = [pc EXCEPT !["Owner"] = "Owner"]

HomeOwner == Owner

SensorTrigger == /\ pc["Sensor"] = "SensorTrigger"
                 /\ \/ /\ doorSensor' = "opened"
                       /\ IF (systemMode /= "disarmed")
                             THEN /\ alarmState' = "sounding"
                                  /\ userNotified' = "notificationSent"
                             ELSE /\ TRUE
                                  /\ UNCHANGED << alarmState, userNotified >>
                       /\ UNCHANGED <<glassBreakSensor, motionStatus>>
                    \/ /\ glassBreakSensor' = "breakageDetected"
                       /\ IF (systemMode /= "disarmed")
                             THEN /\ alarmState' = "sounding"
                                  /\ userNotified' = "notificationSent"
                             ELSE /\ TRUE
                                  /\ UNCHANGED << alarmState, userNotified >>
                       /\ UNCHANGED <<doorSensor, motionStatus>>
                    \/ /\ motionStatus' = "Motion"
                       /\ IF (systemMode = "armedAway")
                             THEN /\ alarmState' = "sounding"
                                  /\ userNotified' = "notificationSent"
                             ELSE /\ TRUE
                                  /\ UNCHANGED << alarmState, userNotified >>
                       /\ TRUE
                       /\ UNCHANGED <<doorSensor, glassBreakSensor>>
                 /\ pc' = [pc EXCEPT !["Sensor"] = "SensorTrigger"]
                 /\ UNCHANGED << cameraStatus, systemMode >>

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
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(HomeOwner)
        /\ WF_vars(Camera)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

LIVENoAlarm == [](~(systemMode = "disarmed" /\ alarmState = "sounding"))
LIVEArmed == <>(alarmState = "disarmed" ~> alarmState = "armedStay")
LIVEAlarm == <>(alarmState = "sounding")

\*WindowBreakAlarm == <>(systemMode = "disarmed" \/ ((systemMode = "armedStay" \/ systemMode = "armedAway") /\ glassBreakSensor = "breakageDetected" /\ alarmState = "sounding"))

=============================================================================
\* Modification History
\* Last modified Wed Dec 20 18:09:17 MSK 2023 by dadro
\* Created Wed Dec 18 12:23:24 MSK 2023 by dadro
