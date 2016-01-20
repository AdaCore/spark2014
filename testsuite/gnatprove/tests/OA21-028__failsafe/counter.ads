with Interfaces; use Interfaces;

package Counter with SPARK_Mode is

   Output : Boolean := False;

   Cycle : constant := 10;

   type Time_Slot_Length is new Unsigned_8 range 0 .. Cycle;
   Count : Time_Slot_Length := 0;

   package Model
      with Ghost is

      subtype Time_Slot is Time_Slot_Length range 1 .. Cycle;

      Inputs : array (Time_Slot) of Boolean;

      function Current_Chain_Length return Time_Slot_Length
      with Post =>
         (if not Inputs (Cycle) then Current_Chain_Length'Result = 0
      else
         (for all I in Cycle - Current_Chain_Length'Result + 1 .. Cycle =>
                Inputs (I))
          and then
            (Current_Chain_Length'Result = Cycle or else
                   not Inputs (Cycle - Current_Chain_Length'Result)));

      procedure Shift_Inputs (Input : Boolean)
        with Post =>
          (for all K in Time_Slot_Length range 1 .. Cycle - 1 =>
             Inputs (K) = Inputs'Old (K + 1))
          and then Inputs (Cycle) = Input;

      function Is_Valid return Boolean is (Current_Chain_Length = Count);
   end Model;

   procedure P (Input : Boolean)
      with Pre => Model.Current_Chain_Length = Count,
     Post => Model.Current_Chain_Length = Count,
     Global => (In_Out => (Model.Inputs, Count));


end Counter;
