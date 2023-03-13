procedure Test_List_Search with SPARK_Mode is

   type List_Cell;
   type List is access List_Cell;
   type List_Cell is record
      Data : Integer;
      Next : List;
   end record;

   Found     : exception;
   Not_Found : exception;

   function Contains (L : access constant List_Cell; V : Integer) return Boolean is
      (L /= null and then (L.Data = V or else Contains (L.Next, V)))
     with Subprogram_Variant => (Structural => L);

   function Eq (L1, L2 : access constant List_Cell) return Boolean is
      ((L1 = null) = (L2 = null)
       and then (L1 = null
         or else (L1.Data = L2.Data and then Eq (L1.Next, L2.Next))))
     with Subprogram_Variant => (Structural => L1);

   function Eq_But_One (L1, L2 : access constant List_Cell) return Boolean is
     (L1 /= null and then L2 /= null
      and then ((L1.Data = L2.Data and then Eq_But_One (L1.Next, L2.Next))
        or else (L1.Data /= L2.Data and then Eq (L1.Next, L2.Next))))
     with Subprogram_Variant => (Structural => L1);

   function Copy (L : access constant List_Cell) return List with
     Import,
     Global => null,
     Post => Eq (L, Copy'Result);

   function At_End (L : access constant List_Cell) return access constant List_Cell is
     (L)
     with Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   procedure Search_And_Swap (L : access List_Cell; V1, V2 : Integer) with
     Post => Normal_Exit,
     Exceptional_Cases =>
       (Not_Found => not Contains (Copy (L)'Old, V1) and Eq (L, Copy (L)'Old),
        Found     => Contains (Copy (L)'Old, V1)
        and (if V1 = V2 then Eq (L, Copy (L)'Old) else Eq_But_One (L, Copy (L)'Old)));

   Normal_Exit : Boolean := False;

   procedure Search_And_Swap (L : access List_Cell; V1, V2 : Integer) is
      L_Old : constant List := Copy (L) with Ghost; --@RESOURCE_LEAK:FAIL
      X_Old : access constant List_Cell := L_Old with Ghost;
      X     : access List_Cell := L;
   begin
      while X /= null loop
         pragma Loop_Invariant
           (Contains (L_Old, V1) = Contains (X_Old, V1));
         pragma Loop_Invariant (Eq (X, X_Old));
         pragma Loop_Invariant
           (if Eq (At_End (X), X_Old) then Eq (At_End (L), L_Old));
         pragma Loop_Invariant
           (if Eq_But_One (At_End (X), X_Old) then Eq_But_One (At_End (L), L_Old));
         if X.Data = V1 then
            pragma Assert (Contains (X_Old, V1));
            X.Data := V2;
            pragma Assert (if V1 = V2 then Eq (X, X_Old) else Eq_But_One (X, X_Old));
            raise Found;
         end if;
         X := X.Next;
         X_Old := X_Old.Next;
      end loop;
      if not Normal_Exit then
         raise Not_Found;
      end if;
   end Search_And_Swap;

begin
   null;
end;
