package body Arrays
is
   pragma Warnings (Off, "* has no effect");

   type Unsigned_Byte is range 0 .. 255;
   type Enum_T        is (Elem_0, Elem_1, Elem_2);

   type Rec is record
      B : Boolean;
      E : Enum_T;
      I : Integer;
   end record;

   type Char_Set     is array (Character) of Boolean;
   type Char_Map     is array (Character) of Character;
   type Enum_Map     is array (Enum_T)    of Enum_T;
   type Enum_Int_Map is array (Enum_T)    of Integer;

   type Multi_Array  is array (Character) of Enum_Map;

   Zero_Enum_Map : constant Enum_Map := Enum_Map'(Elem_2 => Elem_2,
                                                  others => Elem_0);

   type Small_Index_T is range 1 .. 1000;

   type Int_Array is array (Small_Index_T) of Unsigned_Byte;

   type Optional_Int_Array is record
      A      : Int_Array;
      Exists : Boolean;
   end record;

   type Length_T is range 0 .. 5;
   subtype Index_T is Length_T range 1 .. Length_T'Last;
   type String_Body_T is array (Index_T) of Character;
   type String_T is record
      Len  : Length_T;
      Elem : String_Body_T;
   end record;

   type Bool_Map is array (Boolean) of Unsigned_Byte;

   function Random_Array (N: Integer) return Int_Array
     with Ghost,
          Import;


   function Contains_A (S : in Char_Set;
                        C : in Character)
                       return Boolean
     with Post=> Contains_A'Result = S (C)  --  @POSTCONDITION:PASS
   is
   begin
      return S (C);
   end Contains_A;

   function Contains_B (S : in Char_Set;
                        C : in Character)
                       return Boolean
     with Depends => (Contains_B'Result => S,
                      null => C),
          Post    => Contains_B'Result = S (C)  --  @POSTCONDITION:FAIL @COUNTEREXAMPLE
   is
   begin
      return S ('a');
   end Contains_B;

   function Is_Id_1 (M : in Char_Map;
                     C : in Character)
                    return Boolean
     with Post => Is_Id_1'Result = (M (C) = C)  --  @POSTCONDITION:PASS
   is
   begin
      return M (C) = C;
   end Is_Id_1;

   function Is_Id_2 (M : in Char_Map;
                     C : in Character)
                    return Boolean
     with Post => Is_Id_2'Result = (M (C) = C)  --  @POSTCONDITION:FAIL @COUNTEREXAMPLE
   is
   begin
      return M (C) = 'a';
   end Is_Id_2;

   procedure Test_Id_1 (M : in     Char_Map;
                        C : in out Character)
     with Depends => (C =>+ M),
          Pre     => (for all I in Character => M (I) = I)
   is
      C_Old : constant Character := C;
   begin
      C := M (C);
      pragma Assert (C = C_Old);  --  @ASSERT:PASS
   end Test_Id_1;

   procedure Test_Id_2 (M : in     Char_Map;
                        C : in out Character)
     with Depends => (C =>+ M),
          Pre     => (for all I in Character => M (I) = I)
   is
   begin
      C := M (C);
      pragma Assert (C = Character'Val(0));  --  @ASSERT:FAIL @COUNTEREXAMPLE
   end Test_Id_2;

   procedure Test_A (M : in out Char_Map)
     with Depends => (M =>+ null)
   is
   begin
      M ('a') := 'A';
      pragma Assert (M ('a') = 'a');  --  @ASSERT:FAIL @COUNTEREXAMPLE
   end Test_A;

   procedure Test_B (M : in out Enum_Map)
     with Depends => (M =>+ null)
   is
   begin
      M (Elem_0) := Elem_2;
      pragma Assert (M (Elem_0) = Elem_0);  --  @ASSERT:FAIL @COUNTEREXAMPLE
   end Test_B;

   procedure Test_C (MM : in out Multi_Array)
     with Depends => (MM =>+ null)
   is
   begin
      MM ('a') (Elem_0) := Elem_0;
      pragma Assert (MM ('a') (Elem_0) = Elem_1);  --  @ASSERT:FAIL
   end Test_C;

   procedure Test_F (M : out Enum_Map)
     with Depends => (M => null)
   is
   begin
      M := Zero_Enum_Map;
      pragma Assert (M (Elem_1) = Elem_0);  --  @ASSERT:PASS
   end Test_F;

   procedure Test_I (R : in out Optional_Int_Array)
     with Depends => (R =>+ null)
   is
   begin
      R.A (3) := 5;
      pragma Assert (R.Exists);  --  @ASSERT:FAIL @COUNTEREXAMPLE

      pragma Assert (R.A(3) = 5);  --  @ASSERT:PASS

      pragma Assert (R.A(1) = 5);  --  @ASSERT:FAIL @COUNTEREXAMPLE
   end Test_I;

   procedure Test_J (S : in out String_T)
     with Depends => (S =>+ null),
          Pre     => (for all I in Index_T range S.Len + 1..Index_T'Last =>
                        S.Elem (I) = ' ')
                     and S.Len < Length_T'Last,
          Post    => (for all I in Index_T range S.Len + 1..Index_T'Last =>
                        S.Elem (I) = ' ')
   is
   begin
      S.Len := S.Len + 1;
      S.Elem (S.Len) := 'x';
   end Test_J;

    procedure Test_K (S : in String_T)
      with Depends => (null => S),
           Pre     => (for all I in Index_T => S.Elem (I) in 'a'..'z')
                      and S.Len > 1
   is
   begin
      pragma Assert (S.Elem (S.Len) <= 'z');  --  @ASSERT:PASS
      null;
   end Test_K;

   procedure Test_L (A : in Bool_Map)
     with Depends => (null => A)
   is
   begin
      pragma Assert (for some B in Boolean => A (B) > 0);  --  @ASSERT:FAIL
      null;
   end Test_L;

   function Single_Char_Set (C : in Character) return Char_Set
     with Post => (for all I in Character =>
                     Single_Char_Set'Result (I) = (I = C))
   is
      R : Char_Set;
   begin
      for X in Character loop
         R (X) := X = C;

         pragma Loop_Invariant (for all I in Character range  --  @LOOP_INVARIANT_INIT:PASS @LOOP_INVARIANT_PRESERV:PASS
                                  Character'First..X => R (I) = (I = C));
      end loop;
      return R;
   end Single_Char_Set;

   function Single_Char_Set_Broken (C : in Character) return Char_Set
     with Post => (for all I in Character =>
                     Single_Char_Set_Broken'Result (I) = (I > C))  --  @POSTCONDITION:FAIL @COUNTEREXAMPLE
   is
      R : Char_Set;
   begin
      for X in Character loop
         R (X) := X = C;

         pragma Loop_Invariant (for all I in Character range --  @LOOP_INVARIANT_INIT:PASS @LOOP_INVARIANT_PRESERV:PASS
                                  Character'First..X => R (I) = (I = C));
      end loop;
      return R;
   end Single_Char_Set_Broken;

   procedure Use_Array_From_Function_A
     with Depends => null
   is
      A : Char_Set;
   begin
      A := Single_Char_Set ('D');
      pragma Assert (A ('A'));  --  @ASSERT:FAIL
   end Use_Array_From_Function_A;

   procedure Use_Array_From_Function_B
     with Depends => null
   is
      A : Char_Set;
   begin
      A := Single_Char_Set ('D');
      pragma Assert (A ('D'));  --  @ASSERT:PASS
   end Use_Array_From_Function_B;

   procedure Use_Array_From_Function_C
     with Depends => null
   is
      A : Char_Set;
   begin
      A := Single_Char_Set_Broken ('D');
      pragma Assert (A ('A'));  --  @ASSERT:FAIL
   end Use_Array_From_Function_C;

   procedure Use_Array_From_Function_D
     with Depends => null
   is
      A : Char_Set;
   begin
      A := Single_Char_Set_Broken ('A');
      pragma Assert (A ('D'));  --  @ASSERT:PASS
   end Use_Array_From_Function_D;

   procedure Use_Array_From_Function_E
     with Depends => null
   is
      A : Int_Array;
   begin
      A := Int_Array'(others => 0);
      pragma Assert (A = Random_Array (5));  --  @ASSERT:FAIL
   end Use_Array_From_Function_E;

   pragma Warnings (On, "* has no effect");
end Arrays;
