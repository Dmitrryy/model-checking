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
    userNotified = "noNotification",
    petMotionFeature = "off",
    petDetected = "no";
    
define
SAFEWindowBreakAlarm == (systemMode = "armedStay" \/ systemMode = "armedAway") /\ glassBreakSensor = "breakageDetected" => alarmState = "sounding"
SAFEDoorOpenAlarm == (systemMode = "armedStay" \/ systemMode = "armedAway") /\ doorSensor = "opened" => alarmState = "sounding"
SAFEMotionIgnored == (systemMode = "armedStay" \/ systemMode = "disabled") /\ (motionStatus = "Motion" /\ doorSensor /= "opened" /\ glassBreakSensor /= "breakageDetected") => alarmState /= "sounding"
SAFEPetNotDetected == systemMode = "armedAway" /\ petMotionFeature = "on" /\ petDetected = "yes" /\ (doorSensor /= "opened" /\ glassBreakSensor /= "breakageDetected") => alarmState /= "sounding"
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
            petDetected := "no";
            systemMode := "armedStay";
        elsif (userNotified = "notificationSent") then
            (* reset system *)
            systemMode := "disarmed";
            doorSensor := "closed";
            glassBreakSensor := "noBreakage";
            cameraStatus := "off";
            motionStatus := "noMotion";
            alarmState := "off";
            petDetected := "no";
            userNotified := "noNotification";
        elsif (systemMode = "armedStay") then
            (* go away from home *)
            systemMode := "armedAway";
            either
                petMotionFeature := "on";
            or
                petMotionFeature := "off";
            end either;
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
            
            if (petMotionFeature = "on") then
            either
                petDetected := "yes";
            or
                petDetected := "no";
            end either;
            end if;
            
            if (petDetected = "no" /\ systemMode = "armedAway") then
                alarmState := "sounding";
                userNotified := "notificationSent";
            end if;
        or
            skip;
        end either;
    end while;
end process;

end algorithm
*)

\* BEGIN TRANSLATION (chksum(pcal) = "57b63871" /\ chksum(tla) = "31c51823")
VARIABLES doorSensor, glassBreakSensor, cameraStatus, motionStatus, 
          alarmState, systemMode, userNotified, petMotionFeature, petDetected, 
          pc

(* define statement *)
SAFEWindowBreakAlarm == (systemMode = "armedStay" \/ systemMode = "armedAway") /\ glassBreakSensor = "breakageDetected" => alarmState = "sounding"
SAFEDoorOpenAlarm == (systemMode = "armedStay" \/ systemMode = "armedAway") /\ doorSensor = "opened" => alarmState = "sounding"
SAFEMotionIgnored == (systemMode = "armedStay" \/ systemMode = "disabled") /\ (motionStatus = "Motion" /\ doorSensor /= "opened" /\ glassBreakSensor /= "breakageDetected") => alarmState /= "sounding"
SAFEPetNotDetected == systemMode = "armedAway" /\ petMotionFeature = "on" /\ petDetected = "yes" /\ (doorSensor /= "opened" /\ glassBreakSensor /= "breakageDetected") => alarmState /= "sounding"


vars == << doorSensor, glassBreakSensor, cameraStatus, motionStatus, 
           alarmState, systemMode, userNotified, petMotionFeature, 
           petDetected, pc >>

ProcSet == {"Owner"} \cup {"Sensor"}

Init == (* Global variables *)
        /\ doorSensor = "closed"
        /\ glassBreakSensor = "noBreakage"
        /\ cameraStatus = "off"
        /\ motionStatus = "noMotion"
        /\ alarmState = "off"
        /\ systemMode = "disarmed"
        /\ userNotified = "noNotification"
        /\ petMotionFeature = "off"
        /\ petDetected = "no"
        /\ pc = [self \in ProcSet |-> CASE self = "Owner" -> "Owner"
                                        [] self = "Sensor" -> "SensorTrigger"]

Owner == /\ pc["Owner"] = "Owner"
         /\ IF (systemMode = "disarmed")
               THEN /\ doorSensor' = "closed"
                    /\ glassBreakSensor' = "noBreakage"
                    /\ cameraStatus' = "off"
                    /\ motionStatus' = "noMotion"
                    /\ alarmState' = "off"
                    /\ userNotified' = "noNotification"
                    /\ petDetected' = "no"
                    /\ systemMode' = "armedStay"
                    /\ UNCHANGED petMotionFeature
               ELSE /\ IF (userNotified = "notificationSent")
                          THEN /\ systemMode' = "disarmed"
                               /\ doorSensor' = "closed"
                               /\ glassBreakSensor' = "noBreakage"
                               /\ cameraStatus' = "off"
                               /\ motionStatus' = "noMotion"
                               /\ alarmState' = "off"
                               /\ petDetected' = "no"
                               /\ userNotified' = "noNotification"
                               /\ UNCHANGED petMotionFeature
                          ELSE /\ IF (systemMode = "armedStay")
                                     THEN /\ systemMode' = "armedAway"
                                          /\ \/ /\ petMotionFeature' = "on"
                                             \/ /\ petMotionFeature' = "off"
                                     ELSE /\ TRUE
                                          /\ UNCHANGED << systemMode, 
                                                          petMotionFeature >>
                               /\ UNCHANGED << doorSensor, glassBreakSensor, 
                                               cameraStatus, motionStatus, 
                                               alarmState, userNotified, 
                                               petDetected >>
         /\ pc' = [pc EXCEPT !["Owner"] = "Owner"]

HomeOwner == Owner

SensorTrigger == /\ pc["Sensor"] = "SensorTrigger"
                 /\ \/ /\ doorSensor' = "opened"
                       /\ IF (systemMode /= "disarmed")
                             THEN /\ alarmState' = "sounding"
                                  /\ userNotified' = "notificationSent"
                             ELSE /\ TRUE
                                  /\ UNCHANGED << alarmState, userNotified >>
                       /\ UNCHANGED <<glassBreakSensor, motionStatus, petDetected>>
                    \/ /\ glassBreakSensor' = "breakageDetected"
                       /\ IF (systemMode /= "disarmed")
                             THEN /\ alarmState' = "sounding"
                                  /\ userNotified' = "notificationSent"
                             ELSE /\ TRUE
                                  /\ UNCHANGED << alarmState, userNotified >>
                       /\ UNCHANGED <<doorSensor, motionStatus, petDetected>>
                    \/ /\ motionStatus' = "Motion"
                       /\ IF (petMotionFeature = "on")
                             THEN /\ \/ /\ petDetected' = "yes"
                                     \/ /\ petDetected' = "no"
                             ELSE /\ TRUE
                                  /\ UNCHANGED petDetected
                       /\ IF (petDetected' = "no" /\ systemMode = "armedAway")
                             THEN /\ alarmState' = "sounding"
                                  /\ userNotified' = "notificationSent"
                             ELSE /\ TRUE
                                  /\ UNCHANGED << alarmState, userNotified >>
                       /\ UNCHANGED <<doorSensor, glassBreakSensor>>
                    \/ /\ TRUE
                       /\ UNCHANGED <<doorSensor, glassBreakSensor, motionStatus, alarmState, userNotified, petDetected>>
                 /\ pc' = [pc EXCEPT !["Sensor"] = "SensorTrigger"]
                 /\ UNCHANGED << cameraStatus, systemMode, petMotionFeature >>

Sensor == SensorTrigger

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == HomeOwner \/ Sensor
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(HomeOwner)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

LIVENoAlarm == [](~(systemMode = "disarmed" /\ alarmState = "sounding"))
LIVEArmed == <>(alarmState = "disarmed" ~> alarmState = "armedStay")

\*WindowBreakAlarm == <>(systemMode = "disarmed" \/ ((systemMode = "armedStay" \/ systemMode = "armedAway") /\ glassBreakSensor = "breakageDetected" /\ alarmState = "sounding"))

=============================================================================
\* Modification History
\* Last modified Wed Dec 20 20:10:25 MSK 2023 by dadro
\* Created Wed Dec 18 12:23:24 MSK 2023 by dadro
