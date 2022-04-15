package body Scheduler
with SPARK_Mode => On
is

	procedure SignalEventTwice(Event : in out Event_Type'Class) is
	begin
		Signal(Event);
		Signal(Event);
	end SignalEventTwice;

end Scheduler;
