procedure Test_Slide with Spark_Mode is

   type Pos_Arr is array (Integer range <>) of Positive;

   subtype S1 is Pos_Arr (1 .. 10);
   subtype S2 is Pos_Arr (6 .. 15);

   procedure Test_OK is

      procedure P (X : in out S1; B : Boolean) with
        Import,
        Global => null,
        Always_Terminates,
        Potentially_Invalid => X,
        Post => X'Valid_Scalars = B;

      procedure Assign_1 (X : Pos_Arr; Y : out Pos_Arr) with
        Potentially_Invalid => (X, Y),
        Pre => X'Length = Y'Length,
        Post => X'Valid_Scalars = Y'Valid_Scalars;

      procedure Assign_1 (X : Pos_Arr; Y : out Pos_Arr) is
      begin
         Y := X;
      end Assign_1;

      procedure Assign_2 (X : Pos_Arr; Y : out S2) with
        Potentially_Invalid => (X, Y),
        Pre => X'Length = Y'Length,
        Post => X'Valid_Scalars = Y'Valid_Scalars;

      procedure Assign_2 (X : Pos_Arr; Y : out S2) is
      begin
         Y := X;
      end Assign_2;

      procedure Call_1 (X : in out Pos_Arr; B : Boolean) with
        Potentially_Invalid => X,
        Pre => X'Length = 10;

      procedure Call_1 (X : in out Pos_Arr; B : Boolean) is
      begin
         P (X, B);
         pragma Assert (X'Valid_Scalars = B);
      end Call_1;

      procedure Call_2 (X : in out S2; B : Boolean) with
        Potentially_Invalid => X,
        Post => True;

      procedure Call_2 (X : in out S2; B : Boolean) is
      begin
         P (X, B);
         pragma Assert (X'Valid_Scalars = B);
      end Call_2;

      procedure Decl (X : Pos_Arr) with
        Potentially_Invalid => X,
        Pre => X'Length = 10;

      procedure Decl (X : Pos_Arr) is
         Y : S1 := X with Potentially_Invalid;
      begin
         pragma Assert (X'Valid_Scalars = Y'Valid_Scalars);
      end Decl;
   begin
      null;
   end;

   procedure Test_Bad is

      procedure PP (X : in out S1; B : Boolean; P : Positive) with
        Import,
        Global => null,
        Always_Terminates,
        Potentially_Invalid => X,
        Pre => P in S1'Range,
        Post => X (P)'Valid = B;

      procedure Assign_1 (X : Pos_Arr; Y : out Pos_Arr; P : Positive) with
        Potentially_Invalid => (X, Y),
        Pre => X'Length = Y'Length and P in X'Range and P in Y'Range,
        Post => X (P)'Valid = Y (P)'Valid; -- @POSTCONDITION:FAIL

      procedure Assign_1 (X : Pos_Arr; Y : out Pos_Arr; P : Positive) is
      begin
         Y := X;
      end Assign_1;

      procedure Assign_2 (X : Pos_Arr; Y : out S2; P : Positive) with
        Potentially_Invalid => (X, Y),
        Pre => X'Length = Y'Length and P in X'Range and P in Y'Range,
        Post => X (P)'Valid = Y (P)'Valid; -- @POSTCONDITION:FAIL

      procedure Assign_2 (X : Pos_Arr; Y : out S2; P : Positive) is
      begin
         Y := X;
      end Assign_2;

      procedure Call_1 (X : in out Pos_Arr; B : Boolean; P : Positive) with
        Potentially_Invalid => X,
        Pre => X'Length = 10 and P in S1'Range and P in X'Range;

      procedure Call_1 (X : in out Pos_Arr; B : Boolean; P : Positive) is
      begin
         PP (X, B, P);
         pragma Assert (X (P)'Valid = B); -- @ASSERT:FAIL
      end Call_1;

      procedure Call_2 (X : in out S2; B : Boolean; P : Positive) with
        Potentially_Invalid => X,
        Pre => P in S1'Range and P in S2'Range;

      procedure Call_2 (X : in out S2; B : Boolean; P : Positive) is
      begin
         PP (X, B, P);
         pragma Assert (X (P)'Valid = B); -- @ASSERT:FAIL
      end Call_2;

      procedure Decl (X : Pos_Arr; P : Positive) with
        Potentially_Invalid => X,
        Pre => X'Length = 10 and P in X'Range and P in S1'Range;

      procedure Decl (X : Pos_Arr; P : Positive) is
         Y : S1 := X with Potentially_Invalid;
      begin
         pragma Assert (X (P)'Valid = Y (P)'Valid); -- @ASSERT:FAIL
      end Decl;
   begin
      null;
   end;

begin
   null;
end;
