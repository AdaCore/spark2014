package body Uninitialized
  with Refined_State => (State => (Var,
                                   Arr,
                                   Rec))
is
   type Array_T is array (1 .. 10) of Integer;

   type Record_T is record
      Arr : Array_T;
      Boo : Boolean;
   end record;

   Var : Integer;
   Arr : Array_T;
   Rec : Record_T;

   procedure Set (X : in     Integer;
                  Y :    out Integer) is
   begin
      Y := X;
   end Set;


   procedure Init_Var_Warn (X : out Integer) is
   begin
      if True then
         X := 5;
      end if;
      X := X + 1;  --  This should be a warning.
   end Init_Var_Warn;


   procedure Init_Var_Error
     with Global => (Output => Var)
   is
   begin
      if True then
         Var := 5;
      else
         Var := Var + 1;  --  This should be an error.
      end if;
   end Init_Var_Error;


   procedure Init_Var_Warn_2 (X : Integer)
     with Global => (Output => Var)
   is
   begin
      if X > 0 then
         Var := X;
      end if;
   end Init_Var_Warn_2;


   procedure Init_Arr_Warn (An_Arr : out Array_T) is
   begin
      for I in 1 .. 10 loop
         An_Arr (I) := I;  --  This should be a warning.
      end loop;
   end Init_Arr_Warn;


   procedure Init_Arr_Error
     with Global => (Output => Arr)
   is
   begin
      for I in 1 .. 10 loop
         Arr (I) := Arr (I / 2);  --  This should be an error.
      end loop;
   end Init_Arr_Error;


   procedure Init_Record_Warn
     with Global => (Output => Rec)
   is
   begin
      if True then
         Rec.Boo := True;
      end if;
      Rec.Boo := not Rec.Boo;  --  This should be a warning.

      for I in 1 .. 10 loop
         Rec.Arr (I) := I;  --  This should be a warning.
      end loop;
   end Init_Record_Warn;


   procedure Init_Record_Error (A_Rec : out Record_T) is
   begin
      A_Rec.Boo := not A_Rec.Boo;  --  This should be an error.

      for I in 1 .. 10 loop
         A_Rec.Arr (I) := A_Rec.Arr (I / 2);  --  This should be an error.
      end loop;
   end Init_Record_Error;


   procedure Init_Array_Throug_Call_Warn (An_Arr : out Array_T) is
   begin
      for I in 1 .. 10 loop
         Set (I, An_Arr (I));  --  This should be a warning.
      end loop;
   end Init_Array_Throug_Call_Warn;


   procedure Init_Array_Throug_Call_Error (An_Arr : out Array_T) is
   begin
      for I in 1 .. 10 loop
         Set (An_Arr (I / 2), An_Arr (I));  --  This should be an error.
      end loop;
   end Init_Array_Throug_Call_Error;
end Uninitialized;
