package body Update_Legal_4
  with SPARK_Mode,
       Refined_State => (State => (Rec, A, B))
is
   type Record_T is record
      X, Y : Integer;
   end record;

   Rec : Record_T;
   A   : Integer := 1;
   B   : Integer;

   function Create_Rec return Record_T is
      (Record_T'(X => 0, Y => 0));
begin
   Rec := Create_Rec;
   Rec := Rec'Update (X => A, Y => B);
   B   := 1;
end Update_Legal_4;
