procedure Main with SPARK_Mode is

   type Nat_Array is array (Positive range <>) of Natural;

   procedure P (X : out Integer; I : in out Positive) with
     Pre => I < Integer'Last,
     Post => X = 0 and I = I'Old + 1;

   procedure P (X : out Integer; I : in out Positive) is
   begin
      I := I + 1;
      X := 0;
   end P;

   procedure Call_P (A : in out Nat_Array; I : in out Positive) with
     Pre => I in A'Range and A'Last < Integer'Last,
     Post => A (I'Old) = 0 and I = I'Old + 1;

   procedure Call_P (A : in out Nat_Array; I : in out Positive) is
   begin
      P (A (I), I);
   end Call_P;

   procedure Bad_Call_P (A : in out Nat_Array; I : in out Positive) with
     Pre => I in A'Range and A'Last < Integer'Last,
     Post => (if I <= A'Last then A (I) = 0);  --  @POSTCONDITION:FAIL

   procedure Bad_Call_P (A : in out Nat_Array; I : in out Positive) is
   begin
      P (A (I), I);
   end Bad_Call_P;

begin
   null;
end Main;
