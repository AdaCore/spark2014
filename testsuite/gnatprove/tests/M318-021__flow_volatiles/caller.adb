with Tests_External_State; use Tests_External_State;

procedure Caller (A, B, C, D, E : out Integer)
  with SPARK_Mode,
       Global => (In_Out => (State,
                             State_AR,
                             State_AR_EW,
                             State_AW,
                             State_AW_ER)),
       Depends => (State       => State,
                   State_AR    => (State, State_AR),
                   State_AR_EW => State_AR_EW,
                   State_AW    => State_AW,
                   State_AW_ER => State_AW_ER,
                   A => State,
                   B => State_AR,
                   C => State_Ar_Ew,
                   D => State_Aw,
                   E => State_Aw_Er)
is
   Tmp : Integer;
begin
   --  There should be no flow warnings/errors!

   --  Add some assertions. Ones that we shouldn't be able to prove too! :)

   Get (Tmp);
   Set (Tmp);
   Get (Tmp);
   Get (Tmp);

   A := Tmp;

   Get_AR (B);
   Set_AR (A);
   if B > 0 then
      Set_AR (B);
   end if;

   Get_AR_EW (C);
   Set_AR_EW (C);
   Set_AR_EW (C);

   Get_AW (D);
   Set_AW (D);
   Get_AW (D);

   Get_AW_ER (E);
   if E > 0 then
      Get_AW_ER (E);
   end if;
end Caller;
