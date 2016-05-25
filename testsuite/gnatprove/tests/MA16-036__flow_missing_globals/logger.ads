pragma SPARK_Mode;

with Interfaces; use Interfaces;

package Logger is

   --  Log entry contains the 3 inputs and 2 outputs of the velocity
   --  computation.
   type Log_Entry is record
      NGRotations                        : Unsigned_16;
      NGClickTime                        : Unsigned_16;
      Millisecs                          : Unsigned_16;
      EstimatedGroundVelocity            : Long_Float;
      EstimatedGroundVelocityIsAvailable : Boolean;
   end record;

   Max_Log_Entry : constant := 600;
   --  Logger must be able to store 5 mn of events, which arrive at a rate of
   --  one every 500 ms, which makes 600 events maximum.

   type Log_Index is mod Max_Log_Entry;

   type Log_Array is array (Log_Index range <>) of Log_Entry;

   type Log_Database is private;
   --  Datatype storing the log

   function Log_Size return Natural;
   --  @ignore
   --  Returns the size of the log D

   --  Creates an entry from the individual components
   function Make_Entry
     (NGRotations : Unsigned_16;
      NGClickTime : Unsigned_16;
      Millisecs : Unsigned_16;
      estimatedGroundVelocity : Long_Float;
      estimatedGroundVelocityIsAvailable : Boolean) return Log_Entry
   is
      (Log_Entry'(NGRotations => NGRotations,
                  NGClickTime => NGClickTime,
                  Millisecs => Millisecs,
                  EstimatedGroundVelocity => Estimatedgroundvelocity,
                  EstimatedGroundVelocityIsAvailable =>
                    Estimatedgroundvelocityisavailable));

   function Log_Content return Log_Array
   --  @llr Log_Content
   with Post =>
        Log_Content'Result'Last = Log_Index (Log_Size - 1);
private

   type Log_Database is record
      Data  : Log_Array (0 .. Log_Index'Last);
      First : Log_Index;
      Last  : Log_Index;
      Empty : Boolean;
   end record;

   Event_Log : Log_Database :=
     Log_Database'(Data  => (others => Log_Entry'(0, 0, 0, 0.0, False)),
                   First => 0,
                   Last  => 0,
                   Empty => True);

   function Log_Size return Natural is
     (if Event_Log.Empty then
        0
      else
        Natural (Event_Log.Last - Event_Log.First) + 1);

end Logger;
