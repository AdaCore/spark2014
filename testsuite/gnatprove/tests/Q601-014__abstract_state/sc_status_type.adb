
with Fault_Manager;


package body Sc_Status_Type with SPARK_Mode is


    -- Other Operations


   function Read (This : in Object_Type) return Boolean
       --$ return
       --$      V => (  (This.Sc_State.Prime = This.Sc_State.Shadow) ->
       --$                  V = This.Sc_State.Prime
       --$           );
     is

      Result : Boolean;

   begin

      if This.Sc_State.Prime = This.Sc_State.Shadow then
 
         Result := This.Sc_State.Prime;
 
      else
 
         Fault_Manager.Log_Direct_Failure
           (Failure_Data => 27);

         Result := This.Sc_State.Shadow;

      end if;

      return Result;

    end Read;


    procedure Write (This : out Object_Type; Data : in Boolean)
       --$ post
       --$      This.Sc_State.Prime = Data and
       --$      This.Sc_State.Shadow = Data;
       is

   begin

	This.Sc_State.Prime  := Data;
	This.Sc_State.Shadow := Data;

    end Write;


    function Initialise return Object_Type is

   begin
	return Object_Type'(Sc_State =>
			       Duplicate_Status_Type'
				  (Prime => False, Shadow => False));

end Initialise;


begin

   null;

end Sc_Status_Type;
