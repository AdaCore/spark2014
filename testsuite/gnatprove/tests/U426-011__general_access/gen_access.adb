procedure Gen_Access with SPARK_Mode is
   type PS_Int is access Integer;
   type Gen_Int is access all Integer;
   type Cst_Int is access constant Integer;

   function F (X : Gen_Int) return Boolean with Import;
   function F (Dummy : Cst_Int) return Boolean is (True);

   X : PS_Int := new Integer'(12); -- @MEMORY_LEAK:FAIL
   B : Boolean := F (Gen_Int (X));
   Y_1 : Gen_Int := Gen_Int (X);      --  <<< X is moved in the BC, not in proof => memory leak on X
   Y_2 : Gen_Int := new Integer'(12); -- @MEMORY_LEAK:FAIL

   function Mk return Gen_Int with Import;
   Z : Cst_Int := Cst_Int (Mk);      -- @MEMORY_LEAK:NONE
   pragma Assert (F (Cst_Int (Mk))); --  <<< no memory leak

   type Holder is record
      Content : PS_Int;
   end record;
   type Gen_Holder is access all Holder;

   function Mk return not null Gen_Holder with Import;
   P_1 : Gen_Holder := Mk;           -- @MEMORY_LEAK:PASS
   P_2 : Gen_Holder := P_1;          -- @MEMORY_LEAK:FAIL
   Q_1 : Gen_Holder := Mk;           -- @MEMORY_LEAK:PASS

   type Rec_1 is record
      F : Cst_Int;
      G : Gen_Int;
      H : PS_Int;
   end record;
   type Rec_1_Arr is array (Positive range 1 .. 4) of Rec_1;

   function F (Dummy : Rec_1_Arr) return Boolean is (True);
   function Mk_Arr_1 return Rec_1_Arr with Import;
   pragma Assert (F (Mk_Arr_1));     -- @MEMORY_LEAK:FAIL

   type Cst_Acc is access constant Rec_1;
   type Rec_2 is record
      F : Cst_Int;
      G : Gen_Int;
      H : Cst_Acc;
   end record;
   type Rec_2_Arr is array (Positive range 1 .. 4) of Rec_2;

   function F (Dummy : Rec_2_Arr) return Boolean is (True);
   function Mk_Arr_2 return Rec_2_Arr with Import;
   pragma Assert (F (Mk_Arr_2));     -- @MEMORY_LEAK:NONE

   type List;
   type List_Acc is access all List;
   type List is record
      V : PS_Int;
      N : List_Acc;
   end record;
   function Mk_List (I : Integer) return List with Import;
   function F (Dummy : List) return Boolean is (True);
   pragma Assert (F (Mk_List (1)));  -- @MEMORY_LEAK:FAIL
   L1 : List := Mk_List (2);         -- @MEMORY_LEAK:PASS
   L2 : List := L1;                  -- @MEMORY_LEAK:FAIL
   L3 : aliased List := Mk_List (3); --  <<< no memory leak
   L4 : aliased List := Mk_List (4); --  <<< no memory leak,
                                     --  but currently unproved, requires induction
   L5 : aliased List := Mk_List (4); -- @MEMORY_LEAK:PASS

   function At_End (B : access constant List) return access constant List is (B)
     with Ghost, Annotate => (GNATprove, At_End_Borrow);

   function All_Null (L : List) return Boolean is
     (L.V = null and then (if L.N /= null then All_Null (L.N.all)))
   with Annotate => (GNATprove, Terminating);

   procedure Set_All_To_Null (L : aliased in out List) with
     Post => All_Null (L)
   is
      X_Init : access List := L'Access;
      X      : access List := X_Init;
   begin
      loop
         pragma Loop_Invariant (X /= null);
         pragma Loop_Invariant
           (if All_Null (At_End (X).all) then All_Null (At_End (X_Init).all));
         X.V := null; -- @MEMORY_LEAK:FAIL
         X := X.N;
         exit when X = null;
      end loop;
   end Set_All_To_Null;

   procedure Delete (L : in out List) with
     Pre  => All_Null (L),
     Post => L.V = null and L.N = null
   is
   begin
      if L.N /= null then
         Delete (L.N.all);
         L.N := null; -- @MEMORY_LEAK:PASS
      end if;
   end Delete;

   type My_Int is new Integer with Relaxed_Initialization;
   type PS_Int_Rel is access My_Int;
   type List2;
   type List2_Acc is access all List2;
   type List2 is record
      V : PS_Int_Rel;
      N : List_Acc;
   end record;
   function Mk_List2 (I : Integer) return List2 with Import;
   function F (Dummy : List2) return Boolean is (True);
   pragma Assert (F (Mk_List2 (1)));   -- @MEMORY_LEAK:FAIL
   M1 : List2 := Mk_List2 (2);         -- @MEMORY_LEAK:PASS
   M2 : List2 := M1;                   -- @MEMORY_LEAK:FAIL

   type Rec_Rel;
   type My_Acc is access all Rec_Rel;
   type My_Int2 is new Integer with Relaxed_Initialization;
   type Rec_Rel is record
      F1 : My_Int2;
      F2 : PS_Int;
   end record;
   function Mk_My_Acc (I : Integer) return My_Acc with Import;
   function F (Dummy : My_Acc) return Boolean is (True);
   pragma Assert (F (Mk_My_Acc (1)));    -- @MEMORY_LEAK:FAIL
   A1 : My_Acc := Mk_My_Acc (2);         -- @MEMORY_LEAK:PASS
   A2 : My_Acc := A1;                    -- @MEMORY_LEAK:FAIL

begin
   Q_1.Content := null;   -- @MEMORY_LEAK:FAIL
   Set_All_To_Null (L3);
   pragma Assume --  assume fixed length for F3 to help the proof
     (L3.N /= null and then L3.N.N /= null and then L3.N.N.N /= null
      and then L3.N.N.N.N /= null and then L3.N.N.N.N.N /= null
      and then L3.N.N.N.N.N.N = null);
   Set_All_To_Null (L4);
   Set_All_To_Null (L5);
   Delete (L5);  --  useless destruction of an all null list.
                 --  It helps SPARK understand that there are no memory leaks
end Gen_Access;
