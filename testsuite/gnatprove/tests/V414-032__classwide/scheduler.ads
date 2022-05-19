with History;			use History;
with Event_Package;		use Event_Package;

package Scheduler
with SPARK_Mode => On
is

	procedure SignalEventTwice(Event : in out Event_Type'Class) with
		Pre => History.Can_Log(2),
		Post => (Event.Get_Unique_Id = Event.Get_Unique_Id'Old and then
			History.Log = History.Log'Old &
			(Log_Entry'(History.Event_Signaled, Event.Get_Unique_Id) &
			(Log_Entry'(History.Event_Signaled, Event.Get_Unique_Id))));

end Scheduler;
