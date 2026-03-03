pragma Ada_2022;

with SPARK.Containers.Functional.Infinite_Sequences;
with SPARK.Containers.Functional.Sets;
with SPARK.Higher_Order.Reachability;

procedure Reachability_Test with SPARK_Mode
is
   type Cell is record
      V : Integer;
      N : Natural;
   end record;
   function Next (C : Cell) return Natural is (C.N);

   type Memory_Array is array (Positive range <>) of Cell;

   package Memory_Index_Sets is new
     SPARK.Containers.Functional.Sets (Positive);
   use type Memory_Index_Sets.Set;
   package Memory_Index_Sequences is new
     SPARK.Containers.Functional.Infinite_Sequences
       (Positive,
        Use_Logical_Equality => True);
   use type Memory_Index_Sequences.Sequence;

   package Inst_Automated is new
     SPARK.Higher_Order.Reachability
     (Index_Type                            => Positive,
      No_Index                              => 0,
      Cell_Type                             => Cell,
      Memory_Type                           => Memory_Array,
      Next                                  => Next,
      Memory_Index_Sets                     => Memory_Index_Sets,
      Memory_Index_Sequences                => Memory_Index_Sequences,
      Automatically_Instantiate_Definitions => True);

   --  Test that recursive definition of library functions are automatically
   --  available.

   procedure Test_Automated_Def (X : Positive; M : Memory_Array) with
     Pre => X in M'Range and then Inst_Automated.Valid_Memory (M);

   procedure Test_Automated_Def (X : Positive; M : Memory_Array) is
      use Inst_Automated;
   begin
      pragma Assert (Is_Acyclic (X, M) = Is_Acyclic (Next (M (X)), M));
      if Is_Acyclic (X, M) then
         pragma Assert (Reachable_Set (X, M) = Memory_Index_Sets.Add (Reachable_Set (Next (M (X)), M), X));
         pragma Assert (Model (X, M) = Memory_Index_Sequences.Add (Model (Next (M (X)), M), X));
      end if;
   end Test_Automated_Def;

   package Inst_Manual is new
     SPARK.Higher_Order.Reachability
     (Index_Type                            => Positive,
      No_Index                              => 0,
      Cell_Type                             => Cell,
      Memory_Type                           => Memory_Array,
      Next                                  => Next,
      Memory_Index_Sets                     => Memory_Index_Sets,
      Memory_Index_Sequences                => Memory_Index_Sequences,
      Automatically_Instantiate_Definitions => False);

   --  Test that recursive definition of library functions are not
   --  automatically available.

   procedure Test_Manual_Def_1 (X : Positive; M : Memory_Array) with
     Pre => X in M'Range and then Inst_Manual.Valid_Memory (M);

   procedure Test_Manual_Def_1 (X : Positive; M : Memory_Array) is
      use Inst_Manual;
   begin
      pragma Assert (Is_Acyclic (X, M) = Is_Acyclic (Next (M (X)), M)); -- @ASSERT:FAIL
      if Is_Acyclic (X, M) then
         pragma Assert (Reachable_Set (X, M) = Memory_Index_Sets.Add (Reachable_Set (Next (M (X)), M), X)); -- @ASSERT:FAIL
         pragma Assert (Model (X, M) = Memory_Index_Sequences.Add (Model (Next (M (X)), M), X)); -- @ASSERT:FAIL
      end if;
   end Test_Manual_Def_1;

   --  Test that recursive definition of library functions can be retrieved
   --  using manual instantiations of the definition lemmas.

   procedure Test_Manual_Def_2 (X : Positive; M : Memory_Array) with
     Pre => X in M'Range and then Inst_Manual.Valid_Memory (M);

   procedure Test_Manual_Def_2 (X : Positive; M : Memory_Array) is
      use Inst_Manual;
   begin
      Lemma_Is_Acyclic_Def (X, M);
      pragma Assert (Is_Acyclic (X, M) = Is_Acyclic (Next (M (X)), M));
      if Is_Acyclic (X, M) then
         Lemma_Reachable_Def (X, M);
         pragma Assert (Reachable_Set (X, M) = Memory_Index_Sets.Add (Reachable_Set (Next (M (X)), M), X));
         Lemma_Model_Def (X, M);
         pragma Assert (Model (X, M) = Memory_Index_Sequences.Add (Model (Next (M (X)), M), X));
      end if;
   end Test_Manual_Def_2;

   --  Test that recursive definition of library functions can be retrieved
   --  using Disclose_* procedures

   procedure Test_Manual_Def_3 (X : Positive; M : Memory_Array) with
     Pre => X in M'Range and then Inst_Manual.Valid_Memory (M);

   procedure Test_Manual_Def_3 (X : Positive; M : Memory_Array) is
      use Inst_Manual;
   begin
      Disclose_Is_Acyclic;
      pragma Assert (Is_Acyclic (X, M) = Is_Acyclic (Next (M (X)), M));
      if Is_Acyclic (X, M) then

         --  Only Is_Acyclic is disclosed

         pragma Assert (Reachable_Set (X, M) = Memory_Index_Sets.Add (Reachable_Set (Next (M (X)), M), X)); -- @ASSERT:FAIL
         pragma Assert (Model (X, M) = Memory_Index_Sequences.Add (Model (Next (M (X)), M), X)); -- @ASSERT:FAIL
      end if;
   end Test_Manual_Def_3;

   procedure Test_Manual_Def_4 (X : Positive; M : Memory_Array) with
     Pre => X in M'Range and then Inst_Manual.Valid_Memory (M);

   procedure Test_Manual_Def_4 (X : Positive; M : Memory_Array) is
      use Inst_Manual;
   begin
      Disclose_Is_Acyclic;
      Disclose_Reachable;
      Disclose_Model;
      pragma Assert (Is_Acyclic (X, M) = Is_Acyclic (Next (M (X)), M));
      if Is_Acyclic (X, M) then
         pragma Assert (Reachable_Set (X, M) = Memory_Index_Sets.Add (Reachable_Set (Next (M (X)), M), X));
         pragma Assert (Model (X, M) = Memory_Index_Sequences.Add (Model (Next (M (X)), M), X));
      end if;
   end Test_Manual_Def_4;

   procedure Test_Manual_Def_5 (X : Positive; M : Memory_Array) with
     Pre => X in M'Range and then Inst_Manual.Valid_Memory (M);

   procedure Test_Manual_Def_5 (X : Positive; M : Memory_Array) is
      use Inst_Manual;
   begin
      Disclose_Recursive_Definitions;
      pragma Assert (Is_Acyclic (X, M) = Is_Acyclic (Next (M (X)), M));
      if Is_Acyclic (X, M) then
         pragma Assert (Reachable_Set (X, M) = Memory_Index_Sets.Add (Reachable_Set (Next (M (X)), M), X));
         pragma Assert (Model (X, M) = Memory_Index_Sequences.Add (Model (Next (M (X)), M), X));
      end if;
   end Test_Manual_Def_5;

begin
   null;
end Reachability_Test;
