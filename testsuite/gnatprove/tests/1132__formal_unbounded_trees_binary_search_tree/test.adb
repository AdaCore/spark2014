pragma Ada_2022;

with SPARK.Big_Integers;     use SPARK.Big_Integers;
with SPARK.Containers.Types; use SPARK.Containers.Types;
with SPARK.Containers.Functional.Sets;
with SPARK.Containers.Formal.Unbounded_Trees;

procedure Test with SPARK_Mode is

   type Left_Or_Right is (Left, Right);
   package Binary_Trees is new SPARK.Containers.Formal.Unbounded_Trees (Left_Or_Right, Integer);
   use Binary_Trees;
   use Formal_Model;

   procedure Test_Tree is
      T : Tree := Empty_Tree;
   begin
      Insert_Root (T, 1);
      Insert_Child (T, 2, Root (T), Left);
      Insert_Child (T, 3, Root (T), Right);
      Insert_Child (T, 4, Child (T, Root (T), Left), Right);
      pragma Assert (M.Get (Model (T)) = 1);
      pragma Assert (M.Get (M.Child (Model (T), Left)) = 2);
      pragma Assert (M.Get (M.Child (M.Child (Model (T), Left), Right)) = 4);
      pragma Assert (M.Get (M.Child (Model (T), Right)) = 3);
      Replace_Element (T, 5, Child (T, Root (T), Left));
      pragma Assert (M.Get (Model (T)) = 1);
      pragma Assert (M.Get (M.Child (Model (T), Left)) = 5);
      pragma Assert (M.Get (M.Child (M.Child (Model (T), Left), Right)) = 4);
      pragma Assert (M.Get (M.Child (Model (T), Right)) = 3);
      Delete (T, Child (T, Root (T), Left));
      pragma Assert (M.Get (Model (T)) = 1);
      pragma Assert (M.Is_Empty (M.Child (Model (T), Left)));
      pragma Assert (M.Get (M.Child (Model (T), Right)) = 3);
   end Test_Tree;

   package Int_Sets is new SPARK.Containers.Functional.Sets (Integer);
   use Int_Sets;

   function Elements (T : M.Tree) return Int_Sets.Set
   with
     Ghost,
     Subprogram_Variant => (Decreases => (M.Height (T))),
     Post               =>
       (if M.Is_Empty (T)
        then Is_Empty (Elements'Result)
        else
          Elements (M.Child (T, Left)) <= Elements'Result
          and then Elements (M.Child (T, Right)) <= Elements'Result
          and then Contains (Elements'Result, M.Get (T))
          and then (for all E of Elements'Result =>
                      Contains (Elements (M.Child (T, Left)), E)
                      or else Contains (Elements (M.Child (T, Right)), E)
                      or else E = M.Get (T)));

   function Elements (T : M.Tree) return Int_Sets.Set is
   begin
      if M.Is_Empty (T) then
         return Empty_Set;
      else
         return
            R : Int_Sets.Set :=
              Union
                (Elements (M.Child (T, Left)), Elements (M.Child (T, Right)))
         do
            if not Contains (R, M.Get (T)) then
               R := Add (R, M.Get (T));
            end if;
         end return;
      end if;
   end Elements;

   function Is_Search_Tree (T : M.Tree) return Boolean
   is (M.Is_Empty (T)
       or else ((for all V of Elements (M.Child (T, Right)) => M.Get (T) < V)
                and then (for all V of Elements (M.Child (T, Left)) =>
                            M.Get (T) > V)
                and then Is_Search_Tree (M.Child (T, Left))
                and then Is_Search_Tree (M.Child (T, Right))))
   with Subprogram_Variant => (Decreases => M.Height (T)), Ghost;

   function Contains (T : Tree; V : Integer) return Boolean
   with
     Ghost,
     Pre  => Is_Search_Tree (Model (T)),
     Post => Contains'Result = Contains (Elements (Model (T)), V);

   function Contains (T : Tree; V : Integer) return Boolean is
      C : Cursor := Root (T);
   begin
      while Has_Element (T, C) loop
         pragma Loop_Invariant (Is_Search_Tree (Get_Subtree (T, C)));
         pragma
           Loop_Invariant
             (Contains (Elements (Model (T)), V)
                = Contains (Elements (Get_Subtree (T, C)), V));
         pragma Loop_Variant (Decreases => M.Height (Get_Subtree (T, C)));

         if Element (T, C) = V then
            return True;
         elsif V < Element (T, C) then
            C := Child (T, C, Left);
         else
            C := Child (T, C, Right);
         end if;
      end loop;
      return False;
   end Contains;

   procedure Insert (T : in out Tree; V : Integer)
   with
     --  Insertion in a search tree

     Pre  =>
       Is_Search_Tree (Model (T))
       and then (Contains (Elements (Model (T)), V)
                 or else Node_Count (T) < Count_Type'Last),
     Post =>
       Is_Search_Tree (Model (T))
       and then Contains (Elements (Model (T)), V)
       and then Included_Except
                  (Elements (Model (T)), Elements (Model (T'Old)), V)
       and then Elements (Model (T'Old)) <= Elements (Model (T))
       and then Node_Count (T)
                = (if Contains (Elements (Model (T'Old)), V)
                   then Node_Count (T'Old)
                   else Node_Count (T'Old) + 1);

   procedure Insert (T : in out Tree; V : Integer) is

      procedure Reconstruct_Tree_Properties
        (T_Old, T : Tree; C : Cursor; V : Integer)
      with
        --  Reestablish the inductive properties by climbing up the parent chain

        Ghost,
        Subprogram_Variant => (Decreases => K.Length (Get_Path (T_Old, C))),
        Pre                =>
          Has_Element (T_Old, C)
          and then Has_Element (T, C)
          and then Is_Search_Tree (Get_Subtree (T, C))
          and then Contains (Elements (Get_Subtree (T, C)), V)
          and then Included_Except
                     (Elements (Get_Subtree (T, C)),
                      Elements (Get_Subtree (T_Old, C)),
                      V)
          and then Elements (Get_Subtree (T_Old, C))
                   <= Elements (Get_Subtree (T, C))
          and then (for all Prefix of Subtrees (T_Old) =>
                      (if K."<" (Prefix, Get_Path (T_Old, C))
                       then
                         (if K.Get (Get_Path (T_Old, C), K.Length (Prefix) + 1)
                            = Left
                          then M.Get (R.Get (Subtrees (T_Old), Prefix)) > V
                          else M.Get (R.Get (Subtrees (T_Old), Prefix)) < V)))
          and then (for all Prefix of Subtrees (T_Old) =>
                      (if K."<=" (Prefix, Get_Path (T_Old, C))
                       then Is_Search_Tree (R.Get (Subtrees (T_Old), Prefix))))
          and then K."=" (Get_Path (T, C), Get_Path (T_Old, C))
          and then P."<=" (Paths (T_Old), Paths (T))
          and then Subtrees_Preserved_Except
                     (Subtrees (T_Old), Subtrees (T), Get_Path (T_Old, C))
          and then M.Count (Get_Subtree (T, C)) - 1
                   = M.Count (Get_Subtree (T_Old, C)),
        Post               =>
          Is_Search_Tree (Model (T))
          and then Contains (Elements (Model (T)), V)
          and then Included_Except
                     (Elements (Model (T)), Elements (Model (T_Old)), V)
          and then Elements (Model (T_Old)) <= Elements (Model (T))
          and then M.Count (Get_Subtree (T, C)) - 1
                   = M.Count (Get_Subtree (T_Old, C));

      procedure Reconstruct_Tree_Properties
        (T_Old, T : Tree; C : Cursor; V : Integer) is
      begin
         --  Do the proof by induction, a loop would also be possible

         if Is_Root (T_Old, C) then
            return;
         else
            Reconstruct_Tree_Properties (T_Old, T, Parent (T_Old, C), V);
         end if;
      end Reconstruct_Tree_Properties;

      T_Old : constant Tree := T
      with Ghost;
      C     : Cursor := Root (T);
   begin
      if C = No_Element then
         Insert_Root (T, V);
      else
         loop
            pragma Loop_Invariant (Has_Element (T, C));
            pragma
              Loop_Invariant
                (for all Prefix of Subtrees (T) =>
                   (if K."<=" (Prefix, Get_Path (T, C))
                    then Is_Search_Tree (R.Get (Subtrees (T), Prefix))));
            pragma
              Loop_Invariant
                (Contains (Elements (Model (T)), V)
                   = Contains (Elements (Get_Subtree (T, C)), V));
            pragma Loop_Variant (Decreases => M.Height (Get_Subtree (T, C)));
            pragma
              Loop_Invariant
                (for all Prefix of Subtrees (T) =>
                   (if K."<" (Prefix, Get_Path (T, C))
                    then
                      (if K.Get (Get_Path (T, C), K.Length (Prefix) + 1) = Left
                       then M.Get (R.Get (Subtrees (T), Prefix)) > V
                       else M.Get (R.Get (Subtrees (T), Prefix)) < V)));

            if Element (T, C) = V then
               return;
            end if;

            declare
               P : constant Cursor := C;
               W : constant Left_Or_Right :=
                 (if Element (T, C) > V then Left else Right);
            begin
               C := Child (T, C, W);
               if C = No_Element then
                  Insert_Child (T, V, P, W);
                  Reconstruct_Tree_Properties (T_Old, T, P, V);
                  return;
               end if;
            end;
         end loop;
      end if;
   end Insert;

   procedure Remove_Smallest (T : in out Tree; F : Cursor; V : out Integer)
   with
     Subprogram_Variant => (Decreases => M.Height (Get_Subtree (T, F))),
     Pre                =>
       Has_Element (T, F) and then Is_Search_Tree (Get_Subtree (T, F)),
     Post               =>
       (for all CC of Paths (T'Old) =>
          (if not K."<=" (Get_Path (T'Old, F), Get_Path (T'Old, CC))
           then
             P.Has_Key (Paths (T), CC)
             and then K.Logical_Eq
                        (P.Get (Paths (T), CC), P.Get (Paths (T'Old), CC))))
       and then (if Is_Leaf (T'Old, F)
                 then
                   (if Is_Root (T'Old, F)
                    then M.Is_Empty (Model (T))
                    else
                      M.Is_Empty
                        (M.Child
                           (R.Get
                              (Subtrees (T),
                               Formal_Model.Parent (Get_Path (T'Old, F))),
                            K.Get
                              (Get_Path (T'Old, F),
                               K.Last (Get_Path (T'Old, F))))))
                   and then V = M.Get (Get_Subtree (T'Old, F))

                 else
                   Has_Element (T, F)
                   and then K."=" (Get_Path (T, F), Get_Path (T'Old, F))
                   and then Is_Search_Tree (Get_Subtree (T, F))
                   and then (for all E of Elements (Get_Subtree (T, F)) =>
                               E > V)
                   and then Contains (Elements (Get_Subtree (T'Old, F)), V)
                   and then not Contains (Elements (Get_Subtree (T, F)), V)
                   and then Elements (Get_Subtree (T, F))
                            <= Elements (Get_Subtree (T'Old, F))
                   and then Included_Except
                              (Elements (Get_Subtree (T'Old, F)),
                               Elements (Get_Subtree (T, F)),
                               V)
                   and then M.Count (Get_Subtree (T, F))
                            = M.Count (Get_Subtree (T'Old, F)) - 1)
       and then Subtrees_Preserved_Except
                  (Subtrees (T'Old), Subtrees (T), Get_Path (T'Old, F));

   procedure Remove_Smallest (T : in out Tree; F : Cursor; V : out Integer) is

      procedure Reconstruct_Tree_Properties
        (T_Old, T : Tree; F, C : Cursor; V : Integer)
      with
        --  Reestablish the inductive properties by climbing up the parent chain

        Ghost,
        Subprogram_Variant => (Decreases => K.Length (Get_Path (T_Old, C))),
        Pre                =>
          Has_Element (T_Old, C)
          and then Has_Element (T_Old, F)
          and then (K."<=" (Get_Path (T_Old, F), Get_Path (T_Old, C)))
          and then (for all CC of Paths (T_Old) =>
                      (if not K."<" (Get_Path (T_Old, C), Get_Path (T_Old, CC))
                       then
                         P.Has_Key (Paths (T), CC)
                         and then K.Logical_Eq
                                    (P.Get (Paths (T), CC),
                                     P.Get (Paths (T_Old), CC))))
          and then Is_Search_Tree (Get_Subtree (T, C))
          and then (for all Prefix of Subtrees (T_Old) =>
                      (if K."<=" (Get_Path (T_Old, F), Prefix)
                         and K."<=" (Prefix, Get_Path (T_Old, C))
                       then Is_Search_Tree (R.Get (Subtrees (T_Old), Prefix))))
          and then Contains (Elements (Get_Subtree (T_Old, C)), V)
          and then not Contains (Elements (Get_Subtree (T, C)), V)
          and then Elements (Get_Subtree (T, C))
                   <= Elements (Get_Subtree (T_Old, C))
          and then Included_Except
                     (Elements (Get_Subtree (T_Old, C)),
                      Elements (Get_Subtree (T, C)),
                      V)
          and then Subtrees_Preserved_Except
                     (Subtrees (T_Old), Subtrees (T), Get_Path (T_Old, C))
          and then M.Count (Get_Subtree (T, C))
                   = M.Count (Get_Subtree (T_Old, C)) - 1,
        Post               =>
          Is_Search_Tree (Get_Subtree (T, F))
          and then Contains (Elements (Get_Subtree (T_Old, F)), V)
          and then not Contains (Elements (Get_Subtree (T, F)), V)
          and then Elements (Get_Subtree (T, F))
                   <= Elements (Get_Subtree (T_Old, F))
          and then Included_Except
                     (Elements (Get_Subtree (T_Old, F)),
                      Elements (Get_Subtree (T, F)),
                      V)
          and then (for all CC of Paths (T_Old) =>
                      (if not K."<" (Get_Path (T_Old, F), Get_Path (T_Old, CC))
                       then
                         P.Has_Key (Paths (T), CC)
                         and then K.Logical_Eq
                                    (P.Get (Paths (T), CC),
                                     P.Get (Paths (T_Old), CC))))
          and then Subtrees_Preserved_Except
                     (Subtrees (T_Old), Subtrees (T), Get_Path (T_Old, F))
          and then M.Count (Get_Subtree (T, F))
                   = M.Count (Get_Subtree (T_Old, F)) - 1;

      procedure Reconstruct_Tree_Properties
        (T_Old, T : Tree; F, C : Cursor; V : Integer) is
      begin
         --  Do the proof by induction, a loop would also be possible

         if F = C then
            return;
         else
            Reconstruct_Tree_Properties (T_Old, T, F, Parent (T_Old, C), V);
         end if;
      end Reconstruct_Tree_Properties;

      T_Old : constant Tree := T
      with Ghost;
      C     : Cursor := F;
   begin
      loop
         pragma Loop_Invariant (Has_Element (T, C));
         pragma Loop_Invariant (K."<=" (Get_Path (T, F), Get_Path (T, C)));
         pragma
           Loop_Invariant
             (M.Height (Get_Subtree (T, C)) <= M.Height (Get_Subtree (T, F)));
         pragma
           Loop_Invariant
             (for all Prefix of Subtrees (T) =>
                (if K."<=" (Get_Path (T, F), Prefix)
                   and K."<=" (Prefix, Get_Path (T, C))
                 then Is_Search_Tree (R.Get (Subtrees (T), Prefix))));
         pragma
           Loop_Invariant
             (for all Prefix of Subtrees (T) =>
                (if K."<=" (Get_Path (T, F), Prefix)
                   and K."<=" (Prefix, Get_Path (T, C))
                 then
                   M.Get (R.Get (Subtrees (T), Prefix))
                   >= M.Get (Get_Subtree (T, C))));
         pragma
           Loop_Invariant
             (Elements (Get_Subtree (T, C)) <= Elements (Get_Subtree (T, F)));
         pragma
           Loop_Invariant
             (for all E of Elements (Get_Subtree (T, F)) =>
                (if E <= M.Get (Get_Subtree (T, C))
                 then Contains (Elements (Get_Subtree (T, C)), E)));
         pragma Loop_Variant (Decreases => M.Height (Get_Subtree (T, C)));

         if Is_Leaf (T, C) then
            V := Element (T, C);
            Delete (T, C);
            if F /= C then
               pragma Assert (not Is_Root (T_Old, C));
               pragma
                 Assert (Is_Search_Tree (Get_Subtree (T, Parent (T_Old, C))));
               Reconstruct_Tree_Properties (T_Old, T, F, Parent (T_Old, C), V);
            end if;
            return;
         end if;

         declare
            P : constant Cursor := C;
            N : Integer;
         begin
            C := Child (T, C, Left);
            if C = No_Element then
               V := Element (T, P);
               Remove_Smallest (T, Child (T, P, Right), N);
               Replace_Element (T, N, P);
               Reconstruct_Tree_Properties (T_Old, T, F, P, V);
               return;
            end if;
         end;
      end loop;
   end Remove_Smallest;

   procedure Remove_Smallest (T : in out Tree; V : out Integer)
   with
     Pre  => not M.Is_Empty (Model (T)) and then Is_Search_Tree (Model (T)),
     Post =>
       Is_Search_Tree (Model (T))
       and then (for all E of Elements (Model (T)) => E > V)
       and then Contains (Elements (Model (T'Old)), V)
       and then not Contains (Elements (Model (T)), V)
       and then Elements (Model (T)) <= Elements (Model (T'Old))
       and then Included_Except
                  (Elements (Model (T'Old)), Elements (Model (T)), V)
       and then Node_Count (T) = Node_Count (T'Old) - 1;

   procedure Remove_Smallest (T : in out Tree; V : out Integer) is
   begin
      Remove_Smallest (T, Root (T), V);
   end Remove_Smallest;

begin
   Test_Tree;
end Test;
