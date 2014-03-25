with Stack;  use Stack;
package body Array_Aggregates
is
   type Unsigned_Byte is range 0..255;
   type Mod256 is mod 2**8;
   type Enum_T is (Elem_0, Elem_1, Elem_2);

   type Rec is record
      B : Boolean;
      E : Enum_T;
      I : Integer;
   end record;

   type Char_Set is array (Character) of Boolean;
   type Char_Map is array (Character) of Character;
   type Enum_Map is array (Enum_T) of Enum_T;
   type Enum_Int_Map is array (Enum_T) of Integer;
   type Multi_Array is array (Character) of Enum_Map;
   Zero_Enum_Map : constant Enum_Map := Enum_Map'(Elem_2 => Elem_2,
                                                  others => Elem_0);
   type Small_Index_T is range 1..1000;
   type Int_Array is array (Small_Index_T) of Unsigned_Byte;
   type Int_Enum_Array is array (Small_Index_T) of Enum_T;
   type Int_Array_Array is array (Small_Index_T) of Int_Array;

   type Optional_Int_Array is record
      A      : Int_Array;
      Exists : Boolean;
   end record;

   type Length_T is range 0..5;
   subtype Index_T is Length_T range 1..Length_T'Last;
   type String_Body_T is array (Index_T) of Character;

   type String_T is record
      Len  : Length_T;
      Elem : String_Body_T;
   end record;

   type Basic_Record is record
      A : Small_Index_T;
      B : Boolean;
      C : Enum_T;
   end record;

   type Int_Record_Array is array (Small_Index_T) of Basic_Record;
   type Int_String_T_Array is array (Small_Index_T) of String_T;
   type Bool_Map is array (Boolean) of Unsigned_Byte;
   type Int_Private_Array is array (Small_Index_T) of Stack.T;

   pragma Warnings (Off, "* has no effect");
   procedure Aggregate_Test_A
     with Depends => null
   is
      M : Char_Set;
   begin
      M := Char_Set'('a'..'z'       => True,
                     'A'            => False
                       xor Character'('a') = Character'('a'),
                     'N' | 'F'      => True,
                     'L' | 'C'..'E' => True,
                     others         => False or False);
      pragma Assert (M ('a'));  --  @ASSERT:PASS
   end Aggregate_Test_A;
   pragma Warnings (On, "* has no effect");

   pragma Warnings (Off, "* has no effect");
   procedure Aggregate_Test_B
      with Depends => null
   is
      M : Enum_Map;
   begin
      M := Enum_Map'(Elem_0               => Elem_0,
                     Elem_1 | Enum_T'Last => Elem_1);
      pragma Assert (M (Elem_1) = Elem_0);  --  @ASSERT:FAIL
   end Aggregate_Test_B;
   pragma Warnings (On, "* has no effect");

   procedure Aggregate_Test_C (M : out Enum_Map)
     with Depends => (M => null)
   is
   begin
      M := Zero_Enum_Map;
      pragma Assert (M (Elem_1) = Elem_0);  --  @ASSERT:PASS
   end Aggregate_Test_C;

   procedure Aggregate_Test_D (M : out Enum_Map)
     with Depends => (M => null)
   is
   begin
      M := Zero_Enum_Map;
      pragma Assert (M (Elem_1) = Elem_1);  --  @ASSERT:FAIL
   end Aggregate_Test_D;

   procedure Aggregate_Test_E (X : out Int_Array)
     with Depends => (X => null)
   is
   begin
      X := Int_Array'(others => 5 + 3);
      pragma Assert (X (4) = 2);  --  @ASSERT:FAIL
   end Aggregate_Test_E;

   procedure Aggregate_Test_F (X : out Int_Array)
     with Depends => (X => null)
   is
   begin
      X := Int_Array'(others => 5 + 3);
      pragma Assert (X (4) = 16 / 2);  --  @ASSERT:PASS
   end Aggregate_Test_F;

   procedure Aggregate_Test_G (X : out Int_Array)
     with Depends => (X => null)
   is
   begin
      X := Int_Array'(2      => 2,
                      7      => 10,
                      others => 5 + 3);
      pragma Assert (X (4) = 2);  --  @ASSERT:FAIL
   end Aggregate_Test_G;

   procedure Aggregate_Test_H (X : out Int_Array)
     with Depends => (X => null)
   is
   begin
      X := Int_Array'(2      => 2,
                      7      => 10,
                      others => 5 + 3);
      pragma Assert (X (7) = 2);  --  @ASSERT:FAIL
   end Aggregate_Test_H;

   procedure Aggregate_Test_I (X : out Int_Array)
     with Depends => (X => null)
   is
   begin
      X := Int_Array'(2..5   => 2,
                      others => 5 + 3);
      pragma Assert (X (4) = 5);  --  @ASSERT:FAIL
   end Aggregate_Test_I;

   procedure Aggregate_Test_J (X : out Int_Array)
     with Depends => (X => null)
   is
   begin
      X := Int_Array'(2 | 4..6 => 2,
                      others   => 5 + 3);
      pragma Assert (X (5) = 5);  --  @ASSERT:FAIL
   end Aggregate_Test_J;

   procedure Aggregate_Test_K (X : out Int_Array)
     with Depends => (X => null)
   is
   begin
      X := Int_Array'(2 | 4..6 => 2,
                      others   => 5 + 3);
      pragma Assert (X (3) = 5);  --  @ASSERT:FAIL
   end Aggregate_Test_K;

   procedure Aggregate_Test_L (X : out Int_Enum_Array)
     with Depends => (X => null)
   is
   begin
      X := Int_Enum_Array'(2 | 4..6 => Elem_0,
                           others   => Elem_1);
      pragma Assert (X (3) = Elem_2);  --  @ASSERT:FAIL
   end Aggregate_Test_L;

   procedure Aggregate_Test_M (X : out Int_Enum_Array)
     with Depends => (X => null)
   is
   begin
      X := Int_Enum_Array'(2 | 4..6 => Elem_0,
                           others   => Elem_1);
      pragma Assert (X (3) = Elem_1);  --  @ASSERT:PASS
   end Aggregate_Test_M;

   procedure Aggregate_Test_N (X : out Int_Record_Array)
     with Depends => (X => null)
   is
   begin
      X := Int_Record_Array'(2 | 4..6 => Basic_Record'(A => 5,
                                                       B => False,
                                                       C => Elem_0),
                             others   => Basic_Record'(A => 10,
                                                       B => True,
                                                       C => Elem_1));
      pragma Assert (X (3).C = Elem_2);  --  @ASSERT:FAIL
   end Aggregate_Test_N;

   procedure Aggregate_Test_O (X : out Int_Record_Array)
     with Depends => (X => null)
   is
   begin
      X := Int_Record_Array'(2 | 4..6 => Basic_Record'(A => 5,
                                                       B => False,
                                                       C => Elem_0),
                             others   => Basic_Record'(A => 10,
                                                       B => True,
                                                       C => Elem_1));
      pragma Assert (X (3).C = Elem_1);  --  @ASSERT:PASS
   end Aggregate_Test_O;

   procedure Aggregate_Test_P (X : out Int_Array_Array)
     with Depends => (X => null)
   is
   begin
      X := Int_Array_Array'(2 | 4..6 => Int_Array'(1      => 1,
                                                   2      => 2,
                                                   3      => 3,
                                                   others => 0),
                            others   => Int_Array'(5      => 10,
                                                   others => 12));
      pragma Assert (X (3) (4) = 10);  --  @ASSERT:FAIL
   end Aggregate_Test_P;

   procedure Aggregate_Test_Q (X : out Int_Array_Array)
     with Depends => (X => null)
   is
   begin
      X := Int_Array_Array'(2 | 4..6 => Int_Array'(1      => 1,
                                                   2      => 2,
                                                   3      => 3,
                                                   others => 0),
                            others   => Int_Array'(5      => 10,
                                                   others => 12));
      pragma Assert (X (3) (4) = 12);  --  @ASSERT:PASS
   end Aggregate_Test_Q;

   procedure Aggregate_Test_R (X : out Int_Array_Array)
      with Depends => (X => null)
   is
   begin
      X := Int_Array_Array'(others => Int_Array'(5      => 10,
                                                 others => 12));
      pragma Assert (X (3) (4) = 10);  --  @ASSERT:FAIL
   end Aggregate_Test_R;

   procedure Aggregate_Test_S (X : out Int_Array_Array)
     with Depends => (X => null)
   is
   begin
      X := Int_Array_Array'(others => Int_Array'(5      => 10,
                                                 others => 12));
      pragma Assert (X (3) (4) = 12);  --  @ASSERT:PASS
   end Aggregate_Test_S;

   procedure Aggregate_Test_T (X : out Int_Array_Array)
     with Depends => (X => null)
   is
   begin
      X := Int_Array_Array'(others => Int_Array'(others => 12));
      pragma Assert (X (3) (4) = 10);  --  @ASSERT:FAIL
   end Aggregate_Test_T;

   procedure Aggregate_Test_U (X : out Int_Array_Array)
     with Depends => (X => null)
   is
   begin
      X := Int_Array_Array'(others => Int_Array'(others => 12));
      pragma Assert (X (3) (4) = 12);  --  @ASSERT:PASS
   end Aggregate_Test_U;

   procedure Aggregate_Test_V (X : out Int_String_T_Array)
      with Depends => (X => null)
   is
   begin
      X := Int_String_T_Array'(others =>
                                 String_T'(Len  => 5,
                                           Elem => String_Body_T'(1 => 'H',
                                                                  2 => 'e',
                                                                  3 => 'l',
                                                                  4 => 'l',
                                                                  5 => 'o')));
      pragma Assert (X (3).Len = 3);  --  @ASSERT:FAIL
   end Aggregate_Test_V;

   procedure Aggregate_Test_W (X : out Int_String_T_Array)
      with Depends => (X => null)
   is
   begin
      X := Int_String_T_Array'(others =>
                                 String_T'(Len  => 5,
                                           Elem => String_Body_T'(1 => 'W',
                                                                  2 => 'o',
                                                                  3 => 'r',
                                                                  4 => 'l',
                                                                  5 => 'd')));
      pragma Assert (X (3).Len = 5);  --  @ASSERT:PASS
   end Aggregate_Test_W;

   procedure Aggregate_Test_X (X : out Int_Enum_Array)
     with Depends => (X => null)
   is
   begin
      X := Int_Enum_Array'(2 | 4..6           => Elem_0,
                           Small_Index_T'Last => Elem_2,
                           others             => Elem_1);
      pragma Assert (X (1000) = Elem_1);  --  @ASSERT:FAIL
   end Aggregate_Test_X;

   procedure Aggregate_Test_Y (X :    out Int_Enum_Array;
                               N : in     Small_Index_T)
     with Depends => (X => null,
                      null => N)
   is
   begin
      X := Int_Enum_Array'(2 | 4..6           => Elem_0,
                           Small_Index_T'Last => Elem_2,
                           others             => Elem_1);
      pragma Assert (X (N) = Elem_0);  --  @ASSERT:FAIL
   end Aggregate_Test_Y;

   procedure Aggregate_Test_Z (X :    out Int_Enum_Array;
                               N : in     Small_Index_T)
     with Depends => (X => null,
                      null => N)
   is
   begin
      X := Int_Enum_Array'(2 | 4..6           => Elem_0,
                           Small_Index_T'Last => Elem_2,
                           others             => Elem_1);
      pragma Assert (X (N) = Elem_1);  --  @ASSERT:FAIL
   end Aggregate_Test_Z;

   procedure Aggregate_Test_AA (X :    out Int_Enum_Array;
                                N : in     Small_Index_T)
     with Depends => (X => null,
                      null => N)
   is
   begin
      X := Int_Enum_Array'(2 | 4..6           => Elem_0,
                           Small_Index_T'Last => Elem_2,
                           others             => Elem_1);
      pragma Assert (X (N) = Elem_2);  --  @ASSERT:FAIL
   end Aggregate_Test_AA;

   procedure Aggregate_Test_AB (X :    out Int_Enum_Array;
                                N : in     Small_Index_T)
     with Depends => (X => null,
                      null => N)
   is
   begin
      X := Int_Enum_Array'(2 | 4..6           => Elem_0,
                           Small_Index_T'Last => Elem_2,
                           others             => Elem_1);
      pragma Assert (if X (N) /= Elem_1 then X (N) = Elem_2);  --  @ASSERT:FAIL
   end Aggregate_Test_AB;

   procedure Aggregate_Test_AC (X : out Bool_Map)
     with Depends => (X => null)
   is
   begin
      X := Bool_Map'(others => 5);
      pragma Assert (X (True) = 4);  --  @ASSERT:FAIL
   end Aggregate_Test_AC;

   procedure Aggregate_Test_AD (X : out Bool_Map)
     with Depends => (X => null)
   is
   begin
      X := Bool_Map'(False  => 10,
                     others => 5);
      pragma Assert (X (True) = 4);  --  @ASSERT:FAIL
   end Aggregate_Test_AD;

   procedure Aggregate_Test_AE (X : out Bool_Map)
     with Depends => (X => null)
   is
   begin
      X := Bool_Map'(False => 10,
                     True  => 5);
      pragma Assert (X (True) = 4);  --  @ASSERT:FAIL
   end Aggregate_Test_AE;

   procedure Aggregate_Test_AF (X : out Int_Array)
     with Depends => (X => null)
   is
   begin
      X := Int_Array'(1 + 1  => 2,
                      others => 0);
      pragma Assert (X (2) = 3);  --  @ASSERT:FAIL
   end Aggregate_Test_AF;

   procedure Aggregate_Test_AG (X : out Int_Array)
     with Depends => (X => null)
   is
   begin
      X := Int_Array'(1 + 1 .. 10 / 2 => 2,
                      others          => 0);
      pragma Assert (X (2) = 3);  --  @ASSERT:FAIL
   end Aggregate_Test_AG;

   procedure Aggregate_Test_AH (X : out Int_Private_Array)
     with Depends => (X => null)
   is
   begin
      X := Int_Private_Array'(others => Stack.Create_Stack);
      pragma Assert (Stack.Get_Length (X (2)) = 2);  --  @ASSERT:FAIL
   end Aggregate_Test_AH;

   procedure Aggregate_Test_AI (X : out Int_String_T_Array)
     with Depends => (X => null)
   is
   begin
      X := Int_String_T_Array'(others =>
                                 String_T'(Len  => 0,
                                           Elem =>
                                             String_Body_T'(others => ' ')));
      pragma Assert (for all N in Small_Index_T =>  --  @ASSERT:PASS
                       (X (N) = String_T'(Len  => 0,
                                          Elem =>
                                            String_Body_T'(others => ' '))));
   end Aggregate_Test_AI;

   procedure Aggregate_Test_AJ (X : out Int_String_T_Array)
     with Depends => (X => null)
   is
   begin
      X := Int_String_T_Array'(others =>
                                 String_T'(Len  => 0,
                                           Elem =>
                                             String_Body_T'(others => ' ')));
      pragma Assert (for all N in Small_Index_T =>  --  @ASSERT:PASS
                       (X (N) =
                          String_T'(Len  => 0,
                                    Elem => String_Body_T'(1      => ' ',
                                                           others => ' '))));
   end Aggregate_Test_AJ;

   -- Note that counter examples may seem uninitive but this is
   -- another incarnation of the same issue illustrated by:
   --  Array_Equality_Test
   procedure Aggregate_Test_AJ_Simplified
     with Depends => null
   is
   begin
      pragma Assert (String_Body_T'(others => ' ') =  --  @ASSERT:PASS
                       String_Body_T'(1      => ' ',
                                      others => ' '));
      pragma Assert (String_T'(Len  => 0,  --  @ASSERT:PASS
                               Elem => String_Body_T'(others => ' ')) =
                       String_T'(Len  => 0,
                                 Elem => String_Body_T'(1      => ' ',
                                                        others => ' ')));
      null;
   end Aggregate_Test_AJ_Simplified;

   procedure Aggregate_Test_AK (X : out Char_Set)
     with Depends => (X => null)
   is
   begin
      X := Char_Set'(others => True);
      pragma Assert (for all N in Character =>  --  @ASSERT:PASS
                       (X = Char_Set'(others => N = N)));
   end Aggregate_Test_AK;

   procedure Aggregate_Test_AL (X : out    Char_Set;
                                Y :     in Mod256)
     with Depends => (X => Y)
   is
   begin
      X := Char_Set'(others => (Y xor Y) = 0);
      pragma Assert (for all N in Character =>  --  @ASSERT:PASS
                       (X = Char_Set'(others => N = N)));
   end Aggregate_Test_AL;
end Array_Aggregates;
