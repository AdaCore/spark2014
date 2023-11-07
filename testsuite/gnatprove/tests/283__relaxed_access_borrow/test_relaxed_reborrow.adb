with Ada.Unchecked_Deallocation;

procedure Test_Relaxed_Reborrow with SPARK_Mode is

   --  Test relaxed init on local borrowers for deep reborrows

   type Holder is record
      Content : Integer;
   end record;

   type List;
   type List_Access is access List;
   type List is record
      Value : Holder;
      Next  : List_Access;
   end record;

   procedure Free is new Ada.Unchecked_Deallocation (List, List_Access);
   function At_End (X : access constant List) return access constant List is (X) with
     --  Relaxed_Initialization => (X, At_End'Result),
     Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   type R_List;
   type R_List_Access is access R_List;
   type R_List is record
      Value : Holder;
      Next  : R_List_Access;
   end record with
     Relaxed_Initialization;

   procedure Free is new Ada.Unchecked_Deallocation (R_List, R_List_Access);
   function At_End (X : access constant R_List) return access constant R_List is (X) with
     Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   function All_Initialized (L : access constant R_List) return Boolean is
     (L = null or else (L.all'Initialized and then All_Initialized (L.Next)))
   with Ghost,
     Subprogram_Variant => (Structural => L);

   procedure Remove_Last (L : in out List_Access) with
     Pre => L /= null;

   procedure Remove_Last (L : in out List_Access) is
   begin
      if L.Next = null then
         Free (L);
         return;
      end if;
      declare
         X : not null access List := L;
      begin
         loop
            pragma Loop_Invariant (X.Next /= null);
            X := X.Next;
            exit when X.Next = null;
         end loop;
         Free (X.Next);
      end;
   end Remove_Last;

   procedure Remove_Last_2 (L : in out R_List_Access) with
     Pre  => L /= null and then All_Initialized (L),
     Post => L = null or else All_Initialized (L);

   procedure Remove_Last_2 (L : in out R_List_Access) is
   begin
      if L.Next = null then
         Free (L);
         return;
      end if;
      declare
         X : not null access R_List := L with Relaxed_Initialization;
      begin
         loop
            pragma Loop_Invariant (X'Initialized);
            pragma Loop_Invariant (X.Next /= null);
            pragma Loop_Invariant (All_Initialized (X));
            pragma Loop_Invariant
              (if All_Initialized (At_End (X))then All_Initialized (At_End (L)));
            X := X.Next;
            exit when X.Next = null;
         end loop;
         Free (X.Next);
      end;
   end Remove_Last_2;

   procedure Remove_Last_3 (L : in out List_Access) with
     Pre => L /= null;

   procedure Remove_Last_3 (L : in out List_Access) is
   begin
      if L.Next = null then
         Free (L);
         return;
      end if;
      declare
         X : not null access List := L with Relaxed_Initialization; -- @INIT_BY_PROOF:FAIL
      begin
         pragma Assert (X'Initialized); -- Not provable as it would require inductive reasoning.
         loop
            pragma Loop_Invariant (X.Next /= null);
            pragma Loop_Invariant (X'Initialized);
            X := X.Next;
            exit when X.Next = null;
         end loop;
         Free (X.Next);
      end;
   end Remove_Last_3;

   procedure Remove_Last_4 (L : in out R_List_Access) with
     Pre  => L /= null and then All_Initialized (L),
     Post => L = null or else All_Initialized (L); -- @POSTCONDITION:FAIL

   procedure Remove_Last_4 (L : in out R_List_Access) is
   begin
      if L.Next = null then
         Free (L);
         return;
      end if;
      declare
         X : not null access R_List := L with Relaxed_Initialization;
         U : Holder with Relaxed_Initialization;
      begin
         loop
            pragma Loop_Invariant (X'Initialized);
            pragma Loop_Invariant (X.Next /= null);
            pragma Loop_Invariant (All_Initialized (X));
            pragma Loop_Invariant
              (if All_Initialized (At_End (X)) then All_Initialized (At_End (L))); -- @LOOP_INVARIANT_PRESERV:FAIL
            X.Value := U;
            X := X.Next;
            exit when X.Next = null;
         end loop;
         Free (X.Next);
      end;
   end Remove_Last_4;

begin
   null;
end Test_Relaxed_Reborrow;
