package body Search_Trees with SPARK_Mode is

   function Value (T : Search_Tree; I : Index_Type) return Natural is
     (T.Values (I));

   function Ordered_Leafs (T : Search_Tree) return Boolean is
     ((if Size (T.Struct) = 0 then T.Root = 0)
      and then
        (if Size (T.Struct) /= 0 then
              T.Root /= 0 and then Valid_Root (T.Struct, T.Root))
      and then
        (if Size (T.Struct) /= 0 then
             (for all I in Index_Type =>
                  (if Model (T.Struct, T.Root) (I).K then
                     (for all J in Index_Type =>
                        (if Model (T.Struct, T.Root) (J).K
                         and then Model (T.Struct, T.Root) (I).A < Model (T.Struct, T.Root) (J).A
                         then (if Get (Model (T.Struct, T.Root) (J).A,
                                       Length (Model (T.Struct, T.Root) (I).A) + 1)
                               = Left
                               then
                                  T.Values (J) < T.Values (I)
                               else T.Values (J) > T.Values (I))))))));

   function Find_Root (F : Forest; Root, I, J : Index_Type) return Index_Type with
     Ghost,
     Pre  => Valid_Root (F, Root)
     and then Model (F, Root) (I).K and then Model (F, Root) (J).K,
     Post => Model (F, Root) (Find_Root'Result).K
     and Model (F, Root) (Find_Root'Result).A <= Model (F, Root) (I).A
     and Model (F, Root) (Find_Root'Result).A <= Model (F, Root) (J).A
     and (I = Find_Root'Result or else J = Find_Root'Result
          or else Get (Model (F, Root) (I).A, Length (Model (F, Root) (Find_Root'Result).A) + 1)
            /= Get (Model (F, Root) (J).A, Length (Model (F, Root) (Find_Root'Result).A) + 1));

   function Find_Root (F : Forest; Root, I, J : Index_Type) return Index_Type is
      M  : constant Model_Type := Model (F, Root);
      KI : Index_Type := I;
      KJ : Index_Type := J;
   begin
      while KI /= KJ loop
         pragma Loop_Invariant (M (KI).A <= M (I).A);
         pragma Loop_Invariant (M (KI).K);
         pragma Loop_Invariant (M (KJ).A <= M (J).A);
         pragma Loop_Invariant (M (KJ).K);
         pragma Loop_Invariant
           (if Length (M (KI).A) > Length (M (KJ).A) then KJ = J);
         pragma Loop_Invariant
           (if Length (M (KJ).A) > Length (M (KI).A) then KI = I);
         if Length (M (KI).A) > Length (M (KJ).A) then
            KI := Parent (F, KI);
         elsif Length (M (KJ).A) > Length (M (KI).A) then
            KJ := Parent (F, KJ);
         else
            KI := Parent (F, KI);
            KJ := Parent (F, KJ);
         end if;
      end loop;
      return KI;
   end Find_Root;

   procedure Left_Rotate (T : in out Search_Tree; I : Index_Type) is
      X, Y    : Index_Type;
      YL      : Extended_Index_Type;
      Is_Root : constant Boolean := I = T.Root;
      J       : Index_Type := 1;
      D       : Direction := Left;
      F_Ext   : Forest with Ghost;

   begin
      --  X is the subtree located at I

      if Is_Root then
         X := T.Root;
      else
         J := Parent (T.Struct, I);
         D := Position (T.Struct, I);
         Extract (T.Struct, T.Root, J, D, X);
         F_Ext := T.Struct;
      end if;

      --  Y is X's right subtree

      Extract (T.Struct, X, X, Right, Y);

      --  YL is Y's left subtree

      Extract (T.Struct, Y, Y, Left, YL);

      --  Plug Y's left subtree into X's right subtree

      Plug (T.Struct, X, X, Right, YL);

      if not Is_Root then
         Prove_Peek_Preserved (F_Ext, T.Struct, T.Root, J, D);
         F_Ext := T.Struct;
      end if;

      --  Plug X into Y's left subtree

      Plug (T.Struct, Y, Y, Left, X);

      --  Y takes X's place in the tree

      if Is_Root then
         T.Root := Y;
      else
         Prove_Peek_Preserved (F_Ext, T.Struct, T.Root, J, D);
         Plug (T.Struct, T.Root, J, D, Y);
      end if;
   end Left_Rotate;

   procedure Right_Rotate (T : in out Search_Tree; I : Index_Type) is
      X, Y    : Index_Type;
      XR      : Extended_Index_Type;
      Is_Root : constant Boolean := I = Root (T);
      J       : Index_Type := 1;
      D       : Direction := Left;
      F_Ext   : Forest with Ghost;

   begin
      --  Y is the subtree located at I

      if Is_Root then
         Y := T.Root;
      else
         J := Parent (T.Struct, I);
         D := Position (T.Struct, I);
         Extract (T.Struct, T.Root, J, D, Y);
         F_Ext := T.Struct;
      end if;

      --  X is Y's left subtree

      Extract (T.Struct, Y, Y, Left, X);

      --  XR is X's right subtree

      Extract (T.Struct, X, X, Right, XR);

      --  Plug X's right subtree into Y's left subtree

      Plug (T.Struct, Y, Y, Left, XR);

      if not Is_Root then
         Prove_Peek_Preserved (F_Ext, T.Struct, T.Root, J, D);
         F_Ext := T.Struct;
      end if;

      --  Plug Y into X's right subtree

      Plug (T.Struct, X, X, Right, Y);

      --  X takes Y's place in the tree

      if Is_Root then
         T.Root := X;
      else
         Prove_Peek_Preserved (F_Ext, T.Struct, T.Root, J, D);
         Plug (T.Struct, T.Root, J, D, X);
      end if;
   end Right_Rotate;

   function Mem (T : Search_Tree; V : Natural) return Boolean
   is
      Current  : Extended_Index_Type := T.Root;
      Previous : Extended_Index_Type := T.Root with Ghost;
      D        : Direction := Left with Ghost;
   begin
      while Current /= 0 loop
         pragma Loop_Invariant (Model (T.Struct, T.Root) (Current).K);
         pragma Loop_Invariant
           (for all I in Index_Type =>
              (if Model (T.Struct, T.Root) (I).K then
                   (if Model (T.Struct, T.Root) (I).A < Model (T.Struct, T.Root) (Current).A
                    then (if Get (Model (T.Struct, T.Root) (Current).A, Length (Model (T.Struct, T.Root) (I).A) + 1) = Left then
                         V < T.Values (I)
                      else V > T.Values (I)))));
         Previous := Current;
         if V = T.Values (Current) then
            return True;
         elsif V < T.Values (Current) then
            D := Left;
            Current := Peek (T.Struct, Current, Left);
         else
            D := Right;
            Current := Peek (T.Struct, Current, Right);
         end if;
      end loop;
      if Size (T.Struct) /= 0 then
         pragma Assert
           (for all I in Index_Type =>
              (if Model (T.Struct, T.Root) (I).K
               then Model (T.Struct, T.Root) (Find_Root (T.Struct, T.Root, I, Previous)).K));
         Prove_Model_Total (T.Struct, T.Root);
         pragma Assert
           (for all I in Index_Type =>
              (if Model (T.Struct, T.Root) (I).K
               and then Find_Root (T.Struct, T.Root, I, Previous) = Previous
               then Value (T, I) /= V));
      end if;
      return False;
   end Mem;

   procedure Insert
     (T : in out Search_Tree; V : Natural; I : out Extended_Index_Type)
   is
      T_Old : constant Search_Tree := T;
   begin
      if T.Root = 0 then
         Init (T.Struct, I);
         T.Values (I) := V;
         T.Root := I;
         pragma Assert (Ordered_Leafs (T));
         return;
      end if;

      declare
         Current  : Extended_Index_Type := T.Root;
         Previous : Extended_Index_Type := 0;
         D        : Direction := Left;
      begin
         while Current /= 0 loop
            pragma Loop_Invariant (Model (T.Struct, T.Root) (Current).K);
            pragma Loop_Invariant
              (for all I in Index_Type =>
                 (if Model (T.Struct, T.Root) (I).K then
                      (if Model (T.Struct, T.Root) (I).A < Model (T.Struct, T.Root) (Current).A
                       then (if Get (Model (T.Struct, T.Root) (Current).A, Length (Model (T.Struct, T.Root) (I).A) + 1) = Left then
                            V < T.Values (I)
                       else V > T.Values (I)))));
            Previous := Current;
            if V = T.Values (Previous) then
               I := 0;
               pragma Assert (for some I in Index_Type =>
                                Model (T) (I).K
                              and then T.Values (I) = V);
               return;
            elsif V < T.Values (Previous) then
               D := Left;
            else
               D := Right;
            end if;
            Current := Peek (T.Struct, Previous, D);
         end loop;

         Prove_Model_Total (T.Struct, T.Root);

--           pragma Assert
--             (for all I in Index_Type =>
--                (if Model (T.Struct, T.Root) (I).K
--                 then Model (T.Struct, T.Root) (Find_Root (T.Struct, T.Root, I, Previous)).K));
         pragma Assert
           (for all I in Index_Type =>
              (if Model (T.Struct, T.Root) (I).K
               and then Find_Root (T.Struct, T.Root, I, Previous) = Previous
               then Value (T, I) /= V));
         pragma Assert
           (for all I in Index_Type =>
              (if Model (T) (I).K then T.Values (I) /= V));

         Insert (T.Struct, T.Root, Previous, D, I);
         T.Values (I) := V;
         pragma Assert
           (for all I in Index_Type =>
              (if Model (T_Old.Struct, T.Root) (I).K then
                   (for all J in Index_Type =>
                        (if Model (T_Old.Struct, T.Root) (J).K
                         and then Model (T.Struct, T.Root) (I).A < Model (T.Struct, T.Root) (J).A
                         then (if Get (Model (T.Struct, T.Root) (J).A, Length (Model (T.Struct, T.Root) (I).A) + 1) = Left then
                              T.Values (J) < T.Values (I)
                           else T.Values (J) > T.Values (I))))));
         pragma Assert
           (for all I in Index_Type =>
              (if Model (T.Struct, T.Root) (I).K and then I /= Peek (T.Struct, Previous, D) then
                   (for all J in Index_Type =>
                        (if Model (T.Struct, T.Root) (J).K
                         and then Model (T.Struct, T.Root) (I).A < Model (T.Struct, T.Root) (J).A
                         then (if Get (Model (T.Struct, T.Root) (J).A, Length (Model (T.Struct, T.Root) (I).A) + 1) = Left then
                              T.Values (J) < T.Values (I)
                           else T.Values (J) > T.Values (I))))));
         pragma Assert (not Model (T_Old) (I).K);
         pragma Assert (Ordered_Leafs (T));
      end;
   end Insert;

end Search_Trees;
