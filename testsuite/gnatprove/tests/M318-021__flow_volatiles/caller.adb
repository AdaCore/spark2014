with Tests_External_State;

procedure Caller (X : out Integer)
  with SPARK_Mode,
       Global => (In_Out => Tests_External_State.State)
is
   Tmp : Integer;
begin
   Tests_External_State.Get (Tmp);
   Tests_External_State.Set (Tmp);
   Tests_External_State.Get (Tmp);
   Tests_External_State.Set (Tmp);

   X := Tmp;
end Caller;
