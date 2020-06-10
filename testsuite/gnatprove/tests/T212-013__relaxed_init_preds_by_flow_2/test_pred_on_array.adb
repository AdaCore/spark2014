procedure Test_Pred_On_Array with SPARK_Mode is
   type My_Int is new Integer with Relaxed_Initialization;
   type Element is record
      F : My_Int;
      G : Integer;
   end record;
   type E_Arr is array (Positive range <>) of Element with
     Predicate => (for some I in E_Arr'Range => E_Arr (I).G = 15 or else E_Arr (I).F'Initialized);

   procedure Test (X : E_Arr) with Global => null is
   begin
      pragma Assert (if X'First = 1 and X'Last = 1 then X (1).G = 15 or else X (1).F'Initialized);
   end Test;

   procedure P1 (A : Positive) is
      X : E_Arr (1 .. A);
   begin
      Test (X); --  There should be a failed initialization check here
   end P1;

   procedure P2 is
      X : E_Arr (1 .. 2);
   begin
      X (1).G := 15;
      X (2).G := 15;
      Test (X); --  This is OK
   end P2;

   type E_Rec is record
      X, Y, Z : Element;
   end record with
   Predicate => Y.G = 15 or X.F'Initialized or Y.F'Initialized or Z.F'Initialized;

   procedure Test (X : E_Rec) with Global => null is
   begin
      pragma Assert (X.Y.G = 15 or X.X.F'Initialized or X.Y.F'Initialized or X.Z.F'Initialized);
   end Test;

   procedure P3 (A : Positive) is
      X : E_Rec;
   begin
      Test (X); --  There should be a failed initialization check here
   end P3;

   procedure P4 (A : Positive) is
      X : E_Rec;
   begin
      X.Y.G := 15;
      X.X.G := 15;
      X.Z.G := 15;
      Test (X); --  This is OK
   end P4;
begin
   null;
end Test_Pred_On_Array;
