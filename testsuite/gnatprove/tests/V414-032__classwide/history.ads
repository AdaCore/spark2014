package History
with SPARK_Mode => On
is

	type Log_Entry_Type is (Event_Signaled, Some_Other_Log_Entry_Type);

	type Loggable_Type is abstract tagged limited null record;

	function Get_Unique_Id(Loggable : Loggable_Type) return Natural is abstract;

	type Loggable_Type_Ptr is access Loggable_Type;

	type Log_Entry is record
		Entry_Type : Log_Entry_Type;
		Loggable_Unique_Id : Natural;
	end record;

	type Log_Buf is array (Natural range <>) of Log_Entry;

	Max_Entries : Natural := Natural'Last;
	Log : Log_Buf(1 .. 0) with Ghost;

	function Can_Log(Entries : Natural) return Boolean is
		(Log'Length < Max_Entries - Entries) with Ghost;

end History;
