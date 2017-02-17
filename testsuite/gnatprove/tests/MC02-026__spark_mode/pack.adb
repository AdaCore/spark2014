package body Pack
  with Refined_State => (State => Data)
is
   pragma SPARK_Mode (Off);

   Data : Integer;

   procedure P (X : out Integer)
     is
   begin
      null;
   end P;

end Pack;
