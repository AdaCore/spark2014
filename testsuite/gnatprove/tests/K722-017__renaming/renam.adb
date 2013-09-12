package body Renam is

   X : Integer;

   type Rec is record
      A : Integer;
   end record;

   R : Rec;

   procedure K is
      Z : Integer renames X;
      Y : Integer renames R.A;
   begin
      Z := 0;
      Y := 0;
   end K;

   procedure O (M : out Integer)
   is
      pragma SPARK_Mode (Off);
      PM : Integer renames M;

      function F return Integer
      is
      begin
         PM := 1;
         return PM;
      end F;
   begin
      null;
   end O;

   procedure P (M : Integer)
   is
      PM : Integer renames M;

      function F return Integer
      is
      begin
         return PM;
      end F;
   begin
      null;
   end P;

   generic
        X : in out Integer;
   package Q is
        Rx : Integer renames X;
   end Q;

   Z : Integer;

   package RN is new Q (Z);

   procedure U is
   begin
      Z := RN.Rx;
   end U;



end Renam;
