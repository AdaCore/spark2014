with History;
use History;

package Event_Package
with SPARK_Mode => On
is
	type Event_Type is abstract limited new History.Loggable_Type with null record;

	type Event_Type_Ptr is access Event_Type;

	procedure Signal(Event : in out Event_Type) is abstract with
		Pre'Class => History.Can_Log(1),
		Post'Class => (Event.Get_Unique_Id = Event.Get_Unique_Id'Old and then
			(History.Log = History.Log'Old & (Log_Entry'(History.Event_Signaled,
				Event.Get_Unique_Id))));

end Event_Package;
