package body Inl is

   type Range_T is new Integer range 1 .. 10;

   type Record_T is record
      X, Y : Integer;
   end record;

   type Record_Table_T is array (Range_T) of Record_T;
   RT : Record_Table_T;

   type Numerals is range -256 .. 255;
   Min : Numerals  := Numerals'First;
   Foo : constant Numerals := Min;
   subtype Numerals_Nonstatic is Numerals range Min .. Foo;  --  min not OK

   procedure Clear_X (R : in out Record_T) is
   begin
      R.X := 0;
   end Clear_X;

   procedure Call_Clear (I : Range_T) is
      Tmp : Range_T := I;
   begin
      Clear_X (RT (Tmp));  --  OK
   end Call_Clear;

   --  var loop bound also ok
end Inl;
