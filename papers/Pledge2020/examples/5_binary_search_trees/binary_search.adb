package body Binary_Search with SPARK_Mode is

   function "<" (V : Integer; T : access constant Tree) return Boolean is
   begin
      if T = null then
         return True;
      else
         --  Unfold definition of M_Contains to help proof

         pragma Assert
           (for all I in Integer =>
              (if M_Contains (T.Left, I) then M_Contains (T, I)));
         pragma Assert
           (for all I in Integer =>
              (if M_Contains (T.Right, I) then M_Contains (T, I)));

         return V < T.Data and V < T.Left and V < T.Right;
      end if;
   end "<";

   function "<" (T : access constant Tree; V : Integer) return Boolean is
   begin
      if T = null then
         return True;
      else
         --  Unfold definition of M_Contains to help proof

         pragma Assert
           (for all I in Integer =>
              (if M_Contains (T.Left, I) then M_Contains (T, I)));
         pragma Assert
           (for all I in Integer =>
              (if M_Contains (T.Right, I) then M_Contains (T, I)));

         return T.Data < V and T.Left < V and T.Right < V;
      end if;
   end "<";

   function Contains (T : access constant Tree; V : Integer) return Boolean is
      X : access constant Tree := T;
   begin
      while X /= null loop

         --  X is sorted

         pragma Loop_Invariant (Sorted (X));

         --  V is contained in T iff it is contained in X

         pragma Loop_Invariant (M_Contains (T, V) = M_Contains (X, V));

         --  If we have found V, return True

         if X.Data = V then
            return True;

         --  If V is smaller than X.Data search in the left subtree

         elsif V < X.Data then
            X := X.Left;

         --  Else search in the right subtree

         else
            X := X.Right;
         end if;
      end loop;
      return False;
   end Contains;

   function All_V (T : access constant Tree) return Int_Set is
      S : Int_Set;
   begin
      if T = null then
         return S;
      end if;

      --  Get all elements of the left and right subtrees

      S := Union (All_V (T.Left), All_V (T.Right));

      --  Add T.Data if it is not already in S

      if not Contains (S, T.Data) then
         S := Add (S, T.Data);
      end if;
      return S;
   end All_V;

   procedure Insert (T : in out Tree_Acc; V : Integer) is
   begin
      --  If T is null, replace it with a leaf containing V

      if T = null then
         T := new Tree'(Data  => V,
                        Left  => null,
                        Right => null);
         return;
      end if;

      --  Otherwise traverse the tree to find a leaf where V can be inserted

      declare
         X     : access Tree := T;
         --  Local borrower of T

         T_Old : constant Int_Set := All_V (X) with Ghost;
         --  Elements of T

         Seen  : Int_Set with Ghost;
         --  Elements of T that are no longer accessible through X

         L, H  : Int_Option := (Present => False) with Ghost;
         --  Ghost variables to store bounds over the values stored in X

      begin
         --  As a local borrower does not allow to modify the pointer it borrows
         --  (as opposed to modifying the vale designated by this pointer, the
         --  loop needs to stop once a suitable parent is found.

         loop
            --  X cannot be null, or we could not use it to insert V

            pragma Loop_Invariant (X /= null);

            --  X is sorted

            pragma Loop_Invariant (Sorted (X));

            --  All values of X are between L and H

            pragma Loop_Invariant (X < H and L < X);

            --  V is between L and H

            pragma Loop_Invariant (V < H and L < V);

            --  The elements of T_Old are the elements of X plus the elements
            --  of Seen.

            pragma Loop_Invariant
              (Length (Seen) <= Count_Type (Size (X)'Loop_Entry - Size (X)));
            pragma Loop_Invariant
              (for all I in Integer =>
                 (if M_Contains (X, I) then Contains (T_Old, I)));
            pragma Loop_Invariant
              (for all I of Seen => Contains (T_Old, I));
            pragma Loop_Invariant
              (for all I of T_Old => Contains (Seen, I) or M_Contains (X, I));

            --  Seen and X are disjoint

            pragma Loop_Invariant
              (for all I of Seen => not M_Contains (X, I));

            --  Pledge: T necessarily contains the values of Seen, which are
            --  frozen by the borrow, plus the values of X.

            pragma Loop_Invariant
              (Pledge
                 (X, (for all I in Integer =>
                          (if M_Contains (X, I) then M_Contains (T, I)))));
            pragma Loop_Invariant
              (Pledge
                 (X, (for all I of Seen => M_Contains (T, I))));
            pragma Loop_Invariant
              (Pledge
                 (X, (for all I in Integer =>
                          (if M_Contains (T, I) then Contains (Seen, I) or M_Contains (X, I)))));

            --  Pledge: If the values of X remain between L and H, then T
            --  remains sorted.

            pragma Loop_Invariant
              (Pledge
                 (X, (if Sorted (X) and then X < H and then L < X then Sorted (T))));

            --  If V is already in T, T is unchanged

            if X.Data = V then
               return;

            --  If V is smaller than X.Data, we should insert it in X.Left

            elsif V < X.Data then

               --  If X.Left is null, insert V as the left child of X

               if X.Left = null then
                  X.Left := new Tree'(Data  => V,
                                      Left  => null,
                                      Right => null);
                  return;

               --  Otherwise, X becomes X.Left and we continue the search

               else
                  --  Update the ghost structures

                  H := (Present => True, Value => X.Data);
                  Seen := Union (Seen, Add (All_V (X.Right), X.Data));

                  --  Update X

                  X := X.Left;

                  --  Restate the last loop invariant to help provers

                  pragma Assert
                    (Pledge
                       (X, (if Sorted (X) and then X < H and then L < X then Sorted (T))));
               end if;

            --  Otherwise, we should insert it in X.Right

            else

               --  If X.Right is null, insert V as the right child of X

               if X.Right = null then
                  X.Right := new Tree'(Data  => V,
                                       Left  => null,
                                       Right => null);
                  return;

               --  Otherwise, X becomes X.Right and we continue the search

               else
                  --  Update the ghost structures
                  L := (Present => True, Value => X.Data);
                  Seen := Union (Seen, Add (All_V (X.Left), X.Data));

                  --  Update X

                  X := X.Right;

                  --  Restate the last loop invariant to help provers

                  pragma Assert
                    (Pledge
                       (X, (if Sorted (X) and then X < H and then L < X then Sorted (T))));
               end if;
            end if;
         end loop;
      end;
   end Insert;

end Binary_Search;
