procedure Test with SPARK_Mode is

   type Int_Array is array (Positive range <>) of Integer;

   function F (X : Int_Array) return Boolean with
     Import,
     Global => null;

   --  Dynamic bounds

   procedure P (X : in out Int_Array) with
     Import,
     Always_Terminates,
     Global => null,
     Pre => F (X),
     Post => F (X);

   procedure Test_Slice (X : in out Int_Array; I, J : Positive) with
     Pre => I in X'Range and then J in X'Range and then I <= J and then J < Integer'Last
     and then F (X (X'First .. I - 1)) and then F (X (I .. J)) and then F (X (J + 1 .. X'Last)),
     Post => F (X (X'First .. I - 1)) and then F (X (I .. J)) and then F (X (J + 1 .. X'Last));

   procedure Test_Slice (X : in out Int_Array; I, J : Positive) is
   begin
      P (X (I .. J));
   end Test_Slice;

   subtype S is Int_Array (1 .. 100);

   procedure P_2 (X : in out S) with
     Import,
     Always_Terminates,
     Global => null,
     Pre => F (X),
     Post => F (X);

   --  Static bounds in prefix

   procedure Test_Slice_2 (X : in out S; I, J : Positive) with
     Pre => I in X'Range and then J in X'Range and then I <= J and then J < Integer'Last
     and then F (X (X'First .. I - 1)) and then F (X (I .. J)) and then F (X (J + 1 .. X'Last)),
     Post => F (X (X'First .. I - 1)) and then F (X (I .. J)) and then F (X (J + 1 .. X'Last));

   procedure Test_Slice_2 (X : in out S; I, J : Positive) is
   begin
      P (X (I .. J));
   end Test_Slice_2;

   --  Static bounds in slice

   procedure Test_Slice_3 (X : in out Int_Array) with
     Pre => 1 in X'Range and then 101 in X'Range
     and then F (X (1 .. 100)) and then F (X (101 .. X'Last)),
     Post => F (X (1 .. 100)) and then F (X (101 .. X'Last));

   procedure Test_Slice_3 (X : in out Int_Array) is
   begin
      P_2 (X (1 .. 100));
   end Test_Slice_3;

   --  With sliding, there is no reason for the validity F to be preserved

   procedure Test_Slice_4 (X : in out Int_Array) with
     Pre => 4 in X'Range and then 105 in X'Range
     and then F (X (X'First .. 4)) and then F (X (5 .. 104)) and then F (X (105 .. X'Last)),
     Post => F (X (X'First .. 4))
     and then F (X (5 .. 104)) --  @POSTCONDITION:FAIL
     and then F (X (105 .. X'Last));

   procedure Test_Slice_4 (X : in out Int_Array) is
   begin
      P_2 (X (5 .. 104)); --  @PRECONDITION:FAIL
   end Test_Slice_4;
begin
   null;
end;
