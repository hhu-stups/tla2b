---- MODULE microwave ----
EXTENDS Naturals

VARIABLES
magnetron_running,
door_open,
button_locked,
time,
error

allvars == <<magnetron_running, door_open, button_locked, time, error>>

\* Initialisierung - die Mikrowelle ist aus, die Tuer geschlossen
Init ==
    /\ magnetron_running = FALSE
    /\ door_open = FALSE
    /\ button_locked = FALSE
    /\ error = FALSE
    /\ time = 0

\* Repraesentiert den Benutzer, der die Tuer oeffnet
Action_Open_Door ==
    /\ button_locked = FALSE
    /\ magnetron_running = FALSE
    /\ door_open = FALSE
    /\ door_open' = TRUE
    /\ UNCHANGED <<magnetron_running, button_locked, time, error>>
   
\* Repraesentiert den Benutzer, der die Tuer schliesst
Action_Close_Door ==
    /\ door_open = TRUE
    /\ door_open' = FALSE
    /\ UNCHANGED <<magnetron_running, button_locked, time, error>>
    
\* Setzt die Zeit auf die (festen) Werte
\* Wenn die Mikrowelle gestoppt wird, ist die Zeit wieder Null
Action_Change_Time ==
    /\ magnetron_running = FALSE
    /\ \/ /\ time = 180
          /\ time' = 120
       \/ /\ time = 120
          /\ time' = 90
       \/ /\ time = 90
          /\ time' = 60
       \/ /\ time = 60
          /\ time' = 30
       \/ /\ time = 30
          /\ time' = 15
       \/ /\ time = 15
          /\ time' = 180
       \/ /\ time = 0
          /\ time' = 180
    /\ UNCHANGED <<magnetron_running, door_open, button_locked, error>>
    
\* Starten der Mikrowelle: Magnetron an, Knopf gesperrt
Action_Start ==
    /\ error = FALSE                        \* Kein Fehlerzustand    
    /\ magnetron_running = FALSE
    /\ door_open = FALSE                    \* Die Tuer muss geschlossen sein
    /\ time /= 0
    /\ magnetron_running' = TRUE
    /\ button_locked' = TRUE
    /\ UNCHANGED <<door_open, time, error>>

\* Stoppen der Mikrowelle: Magnetron aus, Sperre loesen   
Action_Stop ==
    /\ magnetron_running = TRUE             \* Nur wenn eingeschaltet
    /\ magnetron_running' = FALSE
    /\ button_locked' = FALSE
    /\ time' = 0
    /\ UNCHANGED <<door_open, error>>
    
\* Wenn die Mikrowelle laeuft, stoppt Knopf S sie,
\* wenn sie nicht laeuft, startet S
Action_Button_S ==
    IF magnetron_running = FALSE
    THEN Action_Start
    ELSE Action_Stop
    
\* Ein Fehler tritt auf. Einschalten soll nicht mehr moeglich sein.
\* Fehlerzustand kann nur durch Neustart des Modells verlassen werden
Action_Error ==
    /\ error' = TRUE
    /\ magnetron_running' = FALSE
    /\ UNCHANGED <<door_open, button_locked, time>>
    
\* Tick: Eine Sekunde vergeht
Action_Tick ==
    /\ magnetron_running = TRUE
    /\ IF time /= 1
       THEN /\ time' = time - 1
            /\ UNCHANGED <<door_open, magnetron_running, button_locked, error>>
       ELSE /\ time' = 0                    \* Wenn der Timer 0 erreicht,
            /\ magnetron_running' = FALSE   \* Mikrowelle abschalten
            /\ button_locked' = FALSE       \* Und Sperre loesen
            /\ UNCHANGED <<door_open, error>>
        
Next ==
    \/ Action_Open_Door
    \/ Action_Close_Door
    \/ Action_Change_Time
    \/ Action_Button_S
    \/ Action_Error
    \/ Action_Tick

\* Typinvariante
TypeInvariant ==
    /\ magnetron_running \in BOOLEAN
    /\ door_open \in BOOLEAN
    /\ button_locked \in BOOLEAN
    /\ error \in BOOLEAN
    /\ time \in 0..180

\* Die Spezifikation
\* Start mit Init, dann unendlich viele Next-Schritte
\* - Die ersten drei Fairness Angaben repraesentieren den Benutzer,
\*   der die Mikrowelle verwendet (noetig fuer Liveness Beweise)
\* - Das letzte Fairness Statement bedeutet, dass das Tick-Ereignis
\*   ausgefuehrt werden muss (die Zeit darf nicht stehen bleiben)
Spec == 
    /\ Init
    /\ [][Next]_allvars
    /\ SF_allvars (Action_Change_Time)
    /\ SF_allvars (Action_Button_S)
    /\ SF_allvars (Action_Close_Door)
    /\ SF_allvars (Action_Tick)
    
----
THEOREM Spec => []TypeInvariant
----
\* Die folgenden Statements werden per Modelcheck geprueft

\* Wenn das Magnetron laeuft, ist die Tuer geschlossen
\* und der Knopf gesperrt
Door_Locked_When_Heating == 
    /\ magnetron_running = TRUE => door_open = FALSE
    /\ magnetron_running = TRUE => button_locked = TRUE
    
\* Die Zeit kann nur geaendert werden, wenn die Mikrowelle nicht laeuft
Only_Change_Time_When_Off ==
    magnetron_running = TRUE => \neg ENABLED Action_Change_Time
    
\* Die Mirkowelle laeuft nicht dauerhaft
Not_Constantly_Heating ==
    [] <> (magnetron_running = FALSE)
    
\* Wenn ein Fehler auftritt, heizt die Mikrowelle nicht (mehr)
No_Heating_Error_State ==
    error = TRUE => magnetron_running = FALSE
    
\* Die Mikrowelle kann immer gestoppt werden, wenn sie laeuft
Stopable_At_All_Times ==
    magnetron_running = TRUE => ENABLED Action_Stop
    
\* Wenn die Mikrowelle heizt, ist die Zeit nicht Null
Heating_Time_Not_Zero ==
    magnetron_running = TRUE => time /= 0
    
\* Wenn der Knopf gedrueckt wird beginnt das heizen
\* Wenn der Knopf aktiviert ist wird er irgendwann gedrueckt (Fairness)
button1 == 
    /\ magnetron_running = FALSE
    /\ ENABLED Action_Button_S
    /\ error = FALSE
    => [] <> (magnetron_running = TRUE)
\* Der Knopf ist die einzige Moeglichkeit, das Magnetron zu aktivieren   
button2 ==
    [] (\neg ENABLED Action_Start) => [] (magnetron_running = FALSE)
    
\* Liveness: Es gibt immer einen Punkt in der Zukunft,
\*           an dem die Mikrowelle heizt.
\* (es sei denn, ein Fehler tritt auf)
Alive ==
    [] <> (magnetron_running = TRUE \/ error = TRUE)
====