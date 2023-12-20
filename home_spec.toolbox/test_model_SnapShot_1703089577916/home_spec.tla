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
end define;


fair process HomeOwner = "Owner"
begin
    Owner:
    while (TRUE) do
        either
            if (petMotionFeature = "off") then
                petMotionFeature := "on";
            else
                petMotionFeature := "off";
            end if;
        or
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
        end if;
        end either;
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
        or
            petDetected := "yes";
            if (petMotionFeature = "on") then
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

\* BEGIN TRANSLATION (chksum(pcal) = "fb5ebe1f" /\ chksum(tla) = "be22a70")
VARIABLES doorSensor, glassBreakSensor, cameraStatus, motionStatus, 
          alarmState, systemMode, userNotified, petMotionFeature, petDetected, 
          pc

(* define statement *)
SAFEWindowBreakAlarm == (systemMode = "armedStay" \/ systemMode = "armedAway") /\ glassBreakSensor = "breakageDetected" => alarmState = "sounding"
SAFEDoorOpenAlarm == (systemMode = "armedStay" \/ systemMode = "armedAway") /\ doorSensor = "opened" => alarmState = "sounding"
SAFEMotionIgnored == (systemMode = "armedStay" \/ systemMode = "disabled") /\ (motionStatus = "Motion" /\ doorSensor /= "opened" /\ glassBreakSensor /= "breakageDetected") => alarmState /= "sounding"


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
         /\ \/ /\ IF (petMotionFeature = "off")
                     THEN /\ petMotionFeature' = "on"
                     ELSE /\ petMotionFeature' = "off"
               /\ UNCHANGED <<doorSensor, glassBreakSensor, cameraStatus, motionStatus, alarmState, systemMode, userNotified, petDetected>>
            \/ /\ IF (systemMode = "disarmed")
                     THEN /\ doorSensor' = "closed"
                          /\ glassBreakSensor' = "noBreakage"
                          /\ cameraStatus' = "off"
                          /\ motionStatus' = "noMotion"
                          /\ alarmState' = "off"
                          /\ userNotified' = "noNotification"
                          /\ petDetected' = "no"
                          /\ systemMode' = "armedStay"
                     ELSE /\ IF (userNotified = "notificationSent")
                                THEN /\ systemMode' = "disarmed"
                                     /\ doorSensor' = "closed"
                                     /\ glassBreakSensor' = "noBreakage"
                                     /\ cameraStatus' = "off"
                                     /\ motionStatus' = "noMotion"
                                     /\ alarmState' = "off"
                                     /\ petDetected' = "no"
                                     /\ userNotified' = "noNotification"
                                ELSE /\ IF (systemMode = "armedStay")
                                           THEN /\ systemMode' = "armedAway"
                                           ELSE /\ TRUE
                                                /\ UNCHANGED systemMode
                                     /\ UNCHANGED << doorSensor, 
                                                     glassBreakSensor, 
                                                     cameraStatus, 
                                                     motionStatus, alarmState, 
                                                     userNotified, petDetected >>
               /\ UNCHANGED petMotionFeature
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
                       /\ IF (systemMode = "armedAway")
                             THEN /\ alarmState' = "sounding"
                                  /\ userNotified' = "notificationSent"
                             ELSE /\ TRUE
                                  /\ UNCHANGED << alarmState, userNotified >>
                       /\ UNCHANGED <<doorSensor, glassBreakSensor, petDetected>>
                    \/ /\ petDetected' = "yes"
                       /\ IF (petMotionFeature = "on")
                             THEN /\ alarmState' = "sounding"
                                  /\ userNotified' = "notificationSent"
                             ELSE /\ TRUE
                                  /\ UNCHANGED << alarmState, userNotified >>
                       /\ UNCHANGED <<doorSensor, glassBreakSensor, motionStatus>>
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
\* Last modified Wed Dec 20 19:26:10 MSK 2023 by dadro
\* Created Wed Dec 18 12:23:24 MSK 2023 by dadro
