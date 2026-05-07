procedure Test with SPARK_Mode is
   B, C : Integer;
   A : array (Positive range 1 .. 10) of Integer;

   --  Modifies contract is marked

   function F return Integer with SPARK_Mode => Off, Import;

   procedure Reset_Mode_Off_1 with
     Import,
     Global => (In_Out => A),
     Modifies => (A when F = 0);

   procedure Reset_Mode_Off_2 (G : Boolean) with
     Import,
     Global => (In_Out => (A, B, C)),
     Modifies => (A (F) when G, (B, C));

   procedure Reset_Mode_Off_3 (G : Boolean) with
     Import,
     Global => (In_Out => A),
     Modifies => (A (F) when G);

   --  We reject objects if they are not variables

   type Int_Acc is access Integer;
   type Cst_Acc is access constant Integer;

   type R is record
      F : Int_Acc;
      G : Cst_Acc;
   end record;

   procedure Reset_Constant (X : R) with
     Import,
     Modifies => X;

   procedure Reset_Access_Constant (X : in out R) with
     Import,
     Modifies => X.G.all;

   function Borrow (X : in out R) return access Integer with
     Import,
     Modifies => X;

   --  Modifies should accept abstract states

   package Nested with Abstract_State => State is
      procedure P;
   end Nested;

   package body Nested with Refined_State => (State => X) is
      X : Integer;
      procedure P is
      begin
         X := 34;
      end P;
   end Nested;

   procedure Reset_State (B : Boolean) with
     Global => (In_Out => Nested.State),
     Modifies => (Nested.State when B)
   is
   begin
      if B then
         Nested.P;
      end if;
   end Reset_State;

begin
   null;
end;
