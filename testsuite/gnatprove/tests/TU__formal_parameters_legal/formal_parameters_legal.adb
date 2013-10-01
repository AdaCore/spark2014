package body Formal_Parameters_Legal is
   type Record_T is record
      A, B : Integer;
   end record;

   type Array_T is array (1 .. 10) of Integer;

   procedure Formal_Not_Fully_Initialized (Rec : in out Record_T) is
   begin
      Rec.A := 5;
   end Formal_Not_Fully_Initialized;

   procedure Out_Formal_Read_Before_Initialized (Arr : out Array_T)
     with Post => (for all I in Arr'Range => Arr (I) = Array_T'First)
   is
   begin
      Arr := Array_T'(others => Arr'First);
   end Out_Formal_Read_Before_Initialized;
end Formal_Parameters_Legal;