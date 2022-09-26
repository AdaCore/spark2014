procedure Main
with SPARK_Mode => On
is

   --  If the predicate is "above" the borrowed expression (ie, it applies to a
   --  part of the borrowed object which is not a part of the borrower), it is
   --  checked at the end of the borrow. The check will fail / succeed
   --  depending on the actual value stored in the borrower.

   procedure Test1 with
     Global => null
   is
      type Int_Acc is access Integer with
        Predicate => Int_Acc = null or else Int_Acc.all /= 0;
      type R1 is record
         F, G : Int_Acc;
      end record with
        Predicate => (F = null or else F.all /= 1);
      type R1_Acc is not null access R1;
      type R2 is record
         F : R1_Acc;
         G : Int_Acc;
      end record with
        Predicate => (F.F = null or else F.F.all /= 2);
      type R2_Acc is not null access R2;
      type R3 is record
         F : R2_Acc;
         G : Int_Acc;
      end record with
        Predicate => (F.F.F = null or else F.F.F.all /= 3);
      type R3_Acc is not null access R3;

      procedure P (X : R3_Acc; Y : Integer) is
      begin
         if X.F.F.F = null then
            return;
         elsif Y = 0 then
            declare
               B : access Integer := X.F.F.F; -- @PREDICATE_CHECK:FAIL
            begin
               B.all := Y;
            end;
         elsif Y = 1 then
            declare
               B : access Integer := X.F.F.F; -- @PREDICATE_CHECK:FAIL
            begin
               B.all := Y;
            end;
         elsif Y = 2 then
            declare
               B : access Integer := X.F.F.F; -- @PREDICATE_CHECK:FAIL
            begin
               B.all := Y;
            end;
         elsif Y = 3 then
            declare
               B : access Integer := X.F.F.F; -- @PREDICATE_CHECK:FAIL
            begin
               B.all := Y;
            end;
         else
            declare
               B : access Integer := X.F.F.F;
            begin
               B.all := Y;
            end;
         end if;
      end P;
   begin
      null;
   end Test1;

   --  Inside borrowing traversal functions, check that the predicates hold
   --  independtly of the value of the borrower at end.

   procedure Test2 with
     Global => null
   is
      type Int_Acc is access Integer;
      subtype Int_P0 is Integer with
        Predicate => Int_P0 /= 0;
      subtype Int_Acc_P0 is Int_Acc with
        Predicate => Int_Acc_P0 = null or else Int_Acc_P0.all /= 0;
      type R1 is record
         F, G : Int_Acc;
      end record;
      type R1_P0 is record
         F : Int_Acc_P0;
         G : Int_Acc;
      end record;
      subtype R1_P1 is R1 with
        Predicate => (R1_P1.F = null or else R1_P1.F.all /= 1);
      function F (X : not null access R1) return access Integer is
        (X.F);
      function Bad_F (X : not null access R1_P0) return access Integer is
        (X.F); -- @PREDICATE_CHECK:FAIL
      function Bad_F (X : not null access R1_P1) return access Integer is
        (X.F); -- @PREDICATE_CHECK:FAIL
      type R1_Acc is not null access R1;
      type R1_P1_Acc is not null access R1_P1;
      type R1_P0_Acc is not null access R1_P0;
      type R2 is record
         F : R1_Acc;
         G : Int_Acc;
      end record;
      subtype R2_P2 is R2 with
        Predicate => (R2_P2.F.F = null or else R2_P2.F.F.all /= 2);
      type R2_P0 is record
         F : R1_P0_Acc;
         G : Int_Acc;
      end record;
      type R2_P1 is record
         F : R1_P1_Acc;
         G : Int_Acc;
      end record;
      function Bad_F (X : not null access R2_P2) return access R1 is
        (X.F); -- @PREDICATE_CHECK:FAIL
      function F (X : not null access R2_P0) return access R1_P0 is
        (X.F);
      function F (X : not null access R2_P1) return access R1_P1 is
        (X.F);
      function F (X : not null access R2) return access R1 is
        (X.F);
      function Bad_F (X : not null access R2_P2) return access Integer is
        (X.F.F); -- @PREDICATE_CHECK:FAIL
      function Bad_F (X : not null access R2_P1) return access Integer is
        (X.F.F); -- @PREDICATE_CHECK:FAIL
      function Bad_F (X : not null access R2_P0) return access Integer is
        (X.F.F); -- @PREDICATE_CHECK:FAIL
      function F (X : not null access R2) return access Integer is
        (X.F.F);
      type R2_Acc is not null access R2;
      type R2_P0_Acc is not null access R2_P0;
      type R2_P1_Acc is not null access R2_P1;
      type R2_P2_Acc is not null access R2_P2;
      type R3 is record
         F : R2_Acc;
         G : Int_Acc;
      end record;
      subtype R3_P3 is R3 with
        Predicate => (R3_P3.F.F.F = null or else R3_P3.F.F.F.all /= 3);
      type R3_P2 is record
         F : R2_P2_Acc;
         G : Int_Acc;
      end record;
      type R3_P1 is record
         F : R2_P1_Acc;
         G : Int_Acc;
      end record;
      type R3_P0 is record
         F : R2_P0_Acc;
         G : Int_Acc;
      end record;
      function F (X : not null access R3) return access R2 is
        (X.F);
      function Bad_F (X : not null access R3_P3) return access R2 is
        (X.F); -- @PREDICATE_CHECK:FAIL
      function F (X : not null access R3_P0) return access R2_P0 is
        (X.F);
      function F (X : not null access R3_P1) return access R2_P1 is
        (X.F);
      function F (X : not null access R3_P2) return access R2_P2 is
        (X.F);
      function F (X : not null access R3) return access R1 is
        (X.F.F);
      function Bad_F (X : not null access R3_P3) return access R1 is
        (X.F.F); -- @PREDICATE_CHECK:FAIL
      function F (X : not null access R3_P0) return access R1_P0 is
        (X.F.F);
      function F (X : not null access R3_P1) return access R1_P1 is
        (X.F.F);
      function Bad_F (X : not null access R3_P2) return access R1 is
        (X.F.F); -- @PREDICATE_CHECK:FAIL
      function F (X : not null access R3) return access Integer is
        (X.F.F.F);
      function Bad_F (X : not null access R3_P3) return access Integer is
        (X.F.F.F); -- @PREDICATE_CHECK:FAIL
      function Bad_F (X : not null access R3_P0) return access Integer is
        (X.F.F.F); -- @PREDICATE_CHECK:FAIL
      function Bad_F (X : not null access R3_P1) return access Integer is
        (X.F.F.F); -- @PREDICATE_CHECK:FAIL
      function Bad_F (X : not null access R3_P2) return access Integer is
        (X.F.F.F); -- @PREDICATE_CHECK:FAIL
      function F2 (X : not null access R3) return access Integer is
         V2 : access R2 := X.F;
      begin
         declare
            V1 : access R1 := V2.F;
         begin
            return V1.F;
         end;
      end F2;
      function Bad_F2 (X : not null access R3_P0) return access Integer is
         V2 : access R2_P0 := X.F;
      begin
         declare
            V1 : access R1_P0 := V2.F;
         begin
            return V1.F; -- @PREDICATE_CHECK:FAIL
         end;
      end Bad_F2;
      function Bad_F2 (X : not null access R3_P1) return access Integer is
         V2 : access R2_P1 := X.F;
      begin
         declare
            V1 : access R1_P1 := V2.F;
         begin
            return V1.F; -- @PREDICATE_CHECK:FAIL
         end;
      end Bad_F2;
      function Bad_F2 (X : not null access R3_P2) return access Integer is
         V2 : access R2_P2 := X.F;
      begin
         declare
            V1 : access R1 := V2.F; -- @PREDICATE_CHECK:FAIL
         begin
            return V1.F;
         end;
      end Bad_F2;
      function Bad_F2 (X : not null access R3_P3) return access Integer is
         V2 : access R2 := X.F; -- @PREDICATE_CHECK:FAIL
      begin
         declare
            V1 : access R1 := V2.F;
         begin
            return V1.F;
         end;
      end Bad_F2;
   begin
      null;
   end Test2;

   --  For now, if the predicate is "inside" the borrowed expression (ie, it
   --  applies to a part of the borrowed object which is also a part of the
   --  borrower), it is checked at the beginning of the borrow. The check will
   --  succeed iff the predicate will hold no matter which value will be stored
   --  in the borrower.

   procedure Test3 with
     Global => null
   is
      type Int_Acc is access Integer;
      type R1 is record
         F, G : Int_Acc;
      end record;
      subtype R1_P1 is R1 with
        Predicate => (R1_P1.F = null or else R1_P1.F.all /= 1);
      function F (X : not null access R1) return access Integer is
        (X.F);
      type R1_Acc is not null access R1;
      type R1_P1_Acc is not null access R1_P1;
      type R2 is record
         F : R1_Acc;
         G : Int_Acc;
      end record;
      subtype R2_P2 is R2 with
        Predicate => (R2_P2.F.F = null or else R2_P2.F.F.all /= 2);
      type R2_P1 is record
         F : R1_P1_Acc;
         G : Int_Acc;
      end record;
      function F (X : not null access R2_P1) return access R1_P1 is
        (X.F);
      function F (X : not null access R2) return access R1 is
        (X.F);
      function F (X : not null access R2) return access Integer is
        (X.F.F);
      type R2_Acc is not null access R2;
      type R2_P1_Acc is not null access R2_P1;
      type R2_P2_Acc is not null access R2_P2;
      type R3 is record
         F : R2_Acc;
         G : Int_Acc;
      end record;
      subtype R3_P3 is R3 with
        Predicate => (R3_P3.F.F.F = null or else R3_P3.F.F.F.all /= 3);
      type R3_P2 is record
         F : R2_P2_Acc;
         G : Int_Acc;
      end record;
      type R3_P1 is record
         F : R2_P1_Acc;
         G : Int_Acc;
      end record;
      function F (X : not null access R3) return access R2 is
        (X.F);
      function F (X : not null access R3_P1) return access R2_P1 is
        (X.F);
      function F (X : not null access R3_P2) return access R2_P2 is
        (X.F);
      function F (X : not null access R3) return access R1 is
        (X.F.F);
      function F (X : not null access R3_P1) return access R1_P1 is
        (X.F.F);
      function F (X : not null access R3) return access Integer is
        (X.F.F.F);
      type R3_Acc is not null access R3;
      type R3_P1_Acc is not null access R3_P1;
      type R3_P2_Acc is not null access R3_P2;
      type R3_P3_Acc is not null access R3_P3;

      procedure P_1 (X : R3_Acc; Y : Integer) is
      begin
         if X.F.F.F = null then
            return;
         else
            declare
               B : access Integer := X.F.F.F;
            begin
               B.all := Y;
            end;
         end if;
      end P_1;

      procedure P_2 (X : R3_Acc; Y : Integer) is
      begin
         if X.F.F.F = null then
            return;
         else
            declare
               B : access Integer := F (X).F.F;
            begin
               B.all := Y;
            end;
         end if;
      end P_2;

      procedure P_3 (X : R3_Acc; Y : Integer) is
      begin
         if X.F.F.F = null then
            return;
         else
            declare
               B : access Integer := F (X.F).F;
            begin
               B.all := Y;
            end;
         end if;
      end P_3;

      procedure P_4 (X : R3_Acc; Y : Integer) is
      begin
         if X.F.F.F = null then
            return;
         else
            declare
               B : access Integer := F (X.F.F);
            begin
               B.all := Y;
            end;
         end if;
      end P_4;

      procedure P_5 (X : R3_Acc; Y : Integer) is
      begin
         if X.F.F.F = null then
            return;
         else
            declare
               B : access Integer := F (X.F);
            begin
               B.all := Y;
            end;
         end if;
      end P_5;

      procedure P_6 (X : R3_Acc; Y : Integer) is
      begin
         if X.F.F.F = null then
            return;
         else
            declare
               B : access Integer := F (X).F;
            begin
               B.all := Y;
            end;
         end if;
      end P_6;

      procedure P_7 (X : R3_Acc; Y : Integer) is
      begin
         if X.F.F.F = null then
            return;
         else
            declare
               B : access Integer := F (X);
            begin
               B.all := Y;
            end;
         end if;
      end P_7;

      procedure P_11 (X : R3_P1_Acc; Y : Integer) is
      begin
         if X.F.F.F = null then
            return;
         elsif Y = 1 then
            declare
               B : access Integer := X.F.F.F; -- @PREDICATE_CHECK:FAIL
            begin
               B.all := Y;
            end;
         else
            declare
               B : access Integer := X.F.F.F;
            begin
               B.all := Y;
            end;
         end if;
      end P_11;

      procedure P_12 (X : R3_P1_Acc; Y : Integer) is
      begin
         if X.F.F.F = null then
            return;
         elsif Y = 1 then
            declare
               B : access Integer := F (X).F.F; -- @PREDICATE_CHECK:FAIL
            begin
               B.all := Y;
            end;
         else
            declare
               B : access Integer := F (X).F.F; -- spurious predicate check
            begin
               B.all := Y;
            end;
         end if;
      end P_12;

      procedure P_13 (X : R3_P1_Acc; Y : Integer) is
      begin
         if X.F.F.F = null then
            return;
         elsif Y = 1 then
            declare
               B : access Integer := F (X.F).F; -- @PREDICATE_CHECK:FAIL
            begin
               B.all := Y;
            end;
         else
            declare
               B : access Integer := F (X.F).F; -- spurious predicate check
            begin
               B.all := Y;
            end;
         end if;
      end P_13;

      procedure P_16 (X : R3_P1_Acc; Y : Integer) is
      begin
         if X.F.F.F = null then
            return;
         elsif Y = 1 then
            declare
               B : access Integer := F (X).F; -- @PREDICATE_CHECK:FAIL
            begin
               B.all := Y;
            end;
         else
            declare
               B : access Integer := F (X).F; -- spurious predicate check
            begin
               B.all := Y;
            end;
         end if;
      end P_16;

      procedure P_21 (X : R3_P2_Acc; Y : Integer) is
      begin
         if X.F.F.F = null then
            return;
         elsif Y = 2 then
            declare
               B : access Integer := X.F.F.F; -- @PREDICATE_CHECK:FAIL
            begin
               B.all := Y;
            end;
         else
            declare
               B : access Integer := X.F.F.F;
            begin
               B.all := Y;
            end;
         end if;
      end P_21;

      procedure P_22 (X : R3_P2_Acc; Y : Integer) is
      begin
         if X.F.F.F = null then
            return;
         elsif Y = 2 then
            declare
               B : access Integer := F (X).F.F; -- @PREDICATE_CHECK:FAIL
            begin
               B.all := Y;
            end;
         else
            declare
               B : access Integer := F (X).F.F; -- spurious predicate check
            begin
               B.all := Y;
            end;
         end if;
      end P_22;

      procedure P_24 (X : R3_P2_Acc; Y : Integer) is
      begin
         if X.F.F.F = null then
            return;
         elsif Y = 2 then
            declare
               B : access Integer := F (X.F.F); -- @PREDICATE_CHECK:FAIL
            begin
               B.all := Y;
            end;
         else
            declare
               B : access Integer := F (X.F.F);
            begin
               B.all := Y;
            end;
         end if;
      end P_24;

      procedure P_31 (X : R3_P3_Acc; Y : Integer) is
      begin
         if X.F.F.F = null then
            return;
         elsif Y = 3 then
            declare
               B : access Integer := X.F.F.F; -- @PREDICATE_CHECK:FAIL
            begin
               B.all := Y;
            end;
         else
            declare
               B : access Integer := X.F.F.F;
            begin
               B.all := Y;
            end;
         end if;
      end P_31;

      procedure P_34 (X : R3_P3_Acc; Y : Integer) is
      begin
         if X.F.F.F = null then
            return;
         elsif Y = 3 then
            declare
               B : access Integer := F (X.F.F); -- @PREDICATE_CHECK:FAIL
            begin
               B.all := Y;
            end;
         else
            declare
               B : access Integer := F (X.F.F);
            begin
               B.all := Y;
            end;
         end if;
      end P_34;
   begin
      null;
   end Test3;

   --  The fact that the predicate on the old value of the borrower cannot be
   --  invalidated by the new value of the borrower is checked at reborrow.
   --  The check will succeed iff the predicate will hold no matter which value
   --  will be stored in the borrower after the reborrow.
   --  Test that we are not rejecting more than necessary on simple reborrows
   --  (when the predicate only applies to the current element).

   procedure Test4 with
     Global => null
   is
      type Int_Acc is access all Integer;
      type Cell;
      type List is access Cell;
      type Cell is record
         V : not null Int_Acc;
         N : List;
      end record with
        Predicate => V.all /= 1;

      procedure Set_All_To_Zero (X : List) is
         B : access Cell := X;
      begin
         while B /= null loop
            B.V.all := 0;
            B := B.N;
         end loop;
      end Set_All_To_Zero;

      procedure Set_All_To_Zero_2 (X : List) is
         B : access Cell := X;
      begin
         while B /= null loop
            declare
               I : access Integer := B.V;
            begin
               I.all := 0;
            end;
            B := B.N;
         end loop;
      end Set_All_To_Zero_2;

      procedure Set_All_To_One (X : List) is
         B : access Cell := X;
      begin
         while B /= null loop
            B.V.all := 1; -- @PREDICATE_CHECK:FAIL
            B := B.N;
         end loop;
      end Set_All_To_One;

      procedure Set_All_To_One_2 (X : List) is
         B : access Cell := X;
      begin
         while B /= null loop
            declare
               I : access Integer := B.V; -- @PREDICATE_CHECK:FAIL
            begin
               I.all := 1;
            end;
            B := B.N;
         end loop;
      end Set_All_To_One_2;
   begin
      null;
   end Test4;

   procedure Test5 with
     Global => null
   is
      type Int_Acc is access all Natural;
      type Cell;
      type List is access Cell;
      type Cell is record
         V : not null Int_Acc;
         N : List;
      end record with
        Predicate => N = null or else (V.all <= N.V.all);
      --  Ordered list

      procedure Set_All_To_Zero (X : List) is
         B : access Cell := X;
      begin
         while B /= null loop
            B.V.all := 0;
            B := B.N;
         end loop;
      end Set_All_To_Zero;

      procedure Set_All_To_Zero_2 (X : List) is
         B : access Cell := X;
      begin
         while B /= null loop
            declare
               I : access Natural := B.V;
            begin
               I.all := 0;
            end;
            B := B.N;
         end loop;
      end Set_All_To_Zero_2;
   begin
      null;
   end Test5;

   --  Test that we reject incorrect cases (and non-obvious correct cases) as
   --  designed.

   procedure Test6 with
     Global => null
   is
      type Int_Acc is access all Natural;
      type Cell;
      type List is access Cell;
      type Cell is record
         V : not null Int_Acc;
         N : List;
      end record with
        Predicate => N = null or else N.N = null
          or else (N.N.V.all >= N.V.all);
      --  Strange ordered list (the first element is not ordered)

      procedure Set_All_To_Zero (X : List) is
         B : access Cell := X;
      begin
         while B /= null loop
            B.V.all := 0;
            B := B.N; -- PREDICATE_CHECK:FAIL
         end loop;
      end Set_All_To_Zero;
   begin
      null;
   end Test6;

   procedure Test7 with
     Global => null
   is
      type Int_Acc is access all Natural;
      type Cell;
      type List is access Cell;
      type Cell is record
         V : not null Int_Acc;
         N : List;
      end record with
        Predicate => N = null or else N.N = null
          or else (N.N.V.all <= N.V.all);
      --  Strange ordered list (the first element is not ordered)

      procedure Set_All_To_Zero (X : List) is
         B : access Cell := X;
      begin
         while B /= null loop
            B.V.all := 0;
            B := B.N; -- spurious predicate check, the list stays ordered
         end loop;
      end Set_All_To_Zero;
   begin
      null;
   end Test7;
begin
    null;
end Main;
