procedure Test_Pred_On_Array with SPARK_Mode is
   type Element is new Integer with Relaxed_Initialization;
   type E_Arr is array (Positive range <>) of Element with
     Predicate => (for some I in E_Arr'Range => E_Arr (I)'Initialized);

   procedure Test (X : E_Arr) with Global => null is
   begin
      pragma Assert (if X'First = 1 and X'Last = 1 then X (1)'Initialized);
   end Test;

   procedure P1 (A : Positive) is
      X : E_Arr (1 .. A);
   begin
      Test (X); --  There should be a failed initialization check here
   end P1;

   procedure P2 (A : Positive) is
      X : E_Arr (1 .. A);
   begin
      X (1) := 15;
      Test (X); --  This is OK
   end P2;

   type E_Rec is record
      X, Y, Z : Element;
   end record with
   Predicate => X'Initialized or Y'Initialized or Z'Initialized;

   procedure Test (X : E_Rec) with Global => null is
   begin
      pragma Assert (X.X'Initialized or X.Y'Initialized or X.Z'Initialized);
   end Test;

   procedure P3 (A : Positive) is
      X : E_Rec;
   begin
      Test (X); --  There should be a failed initialization check here
   end P3;

   procedure P4 (A : Positive) is
      X : E_Rec;
   begin
      X.Y := 15;
      Test (X); --  This is OK
   end P4;
begin
   null;
end Test_Pred_On_Array;
