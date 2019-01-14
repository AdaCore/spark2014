package Test
with
   Abstract_State => (Valid, State)
is

   function Is_Valid return Boolean; -- with Global => Valid;

   procedure Get_Current_Time
     (Schedule_Ticks :     Integer;
      Correction     : out Integer)
   with
      Global  => (Proof_In => Valid,
                  Input    => State),
      Depends => (Correction => (Schedule_Ticks, State)),
      Pre     => Is_Valid;

private

   State_Valid : Boolean := False
   with
      Part_Of => Valid;

   function Is_Valid return Boolean is (State_Valid);

end Test;
