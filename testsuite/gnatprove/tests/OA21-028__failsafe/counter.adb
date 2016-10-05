package body Counter with SPARK_Mode is

   package body Model is
      function Current_Chain_Length return Time_Slot_Length is
         Res : Time_Slot_Length := 0;
      begin
         while Res < Cycle and then Inputs (Cycle - Res) loop
            pragma Loop_Variant (Increases => Res);
            pragma Loop_Invariant ((for all I in Cycle - Res .. Cycle => Inputs (I)));
            Res := Res + 1;
         end loop;
         return Res;
      end Current_Chain_Length;

      procedure Shift_Inputs (Input : Boolean) is
      begin
         for I in Time_Slot_Length range 1 .. Cycle - 1 loop
            pragma Loop_Invariant
              ((for all K in Time_Slot_Length range 1 .. I - 1 =>
                    Inputs (K) = Inputs'Loop_Entry (K + 1))
               and then
                 (for all K in Time_Slot_Length range I .. Cycle =>
                      Inputs (K) = Inputs'Loop_Entry (K)));
            Inputs (I) := Inputs (I + 1);
         end loop;
         Inputs (Cycle) := Input;

      end Shift_Inputs;

   end Model;

   procedure P (Input : Boolean) is
   begin
      Model.Shift_Inputs (Input);
      if not Input then
         Count := 0;
      elsif Count < Cycle then
         Count := Count + 1;
      end if;
      declare
         A : constant Time_Slot_Length := Model.Current_Chain_Length
           with Ghost;
         use Model;
      begin
         pragma Assert (if Input then
                           (for all I in Cycle - A + 1 .. Cycle => Inputs (I)));
         pragma Assert (if Input then
                       A = Cycle or else not Inputs (Cycle - A));
         pragma Assert (if Input and then Count < Cycle then
                           Model.Current_Chain_Length = Count);
      end;
   end P;

end Counter;
