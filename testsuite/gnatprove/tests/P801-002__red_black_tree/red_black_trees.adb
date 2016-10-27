package body Red_Black_Trees with SPARK_Mode is

   procedure Insert (T : in out Rbt; V : Natural) is
      X, Y : Extended_Index_Type;

   begin
      Insert (T.Struct, V, X);
      if X = Empty then
         return;
      end if;
      T.Color (X) := Red;

      pragma Assert
        (for all I in Index_Type =>
           (if I /= X
            and then
              (Parent (T.Struct, I) = Empty
               or else T.Color (Parent (T.Struct, I)) = Red)
            then T.Color (I) = Black));

      --  X is red, while the parent of X is red, the invariant is broken

      while X /= Root (T.Struct) and then Color (T, Parent (T.Struct, X)) = Red loop
         pragma Loop_Invariant (X /= Empty);
         pragma Loop_Invariant (Size (T.Struct) = Size (T.Struct)'Loop_Entry);
         pragma Loop_Invariant (Root (T.Struct) = Root (T.Struct)'Loop_Entry);
         pragma Loop_Invariant (Model (T.Struct) (X).K);
         pragma Loop_Invariant (Color (T, X) = Red);
         pragma Loop_Invariant (Color (T, Root (T.Struct)) = Black);
         pragma Loop_Invariant
           (for all I in Index_Type =>
              (if I /= X
               and then
                 (Parent (T.Struct, I) = Empty
                  or else T.Color (Parent (T.Struct, I)) = Red)
               then T.Color (I) = Black));
         pragma Loop_Invariant (Values (T.Struct) = Values (T.Struct)'Loop_Entry);

         if Position (T.Struct, Parent (T.Struct, X)) = Left then

            --  Y is X's uncle

            Y := Peek (T.Struct, Parent (T.Struct, Parent (T.Struct, X)), Right);
            if Color (T, Y) = Red then

               --  If Y is red, move both Y and X's parent to black and the
               --  grand parent to Red. This preserves the number of black node
               --  per branch.

               T.Color (Y) := Black;
               T.Color (Parent (T.Struct, X)) := Black;
               T.Color (Parent (T.Struct, Y)) := Red;

               --  The grand parent may now break the invariant

               X := Parent (T.Struct, Y);
            else

               --  Y is black. We will color the grand parent red and rotate it
               --  to the right. To do so, we need the right son of the parent
               --  to be black. If it is X, it is red, so we need to first
               --  rotate it to the left.

               if X = Peek (T.Struct, Parent (T.Struct, X), Right) then
                  X := Parent (T.Struct, X);
                  Left_Rotate (T.Struct, X);
               end if;

               pragma Assert (Parent (T.Struct, Parent (T.Struct, X)) /= Empty);
               pragma Assert (Peek (T.Struct,
                              Parent (T.Struct, Parent (T.Struct, X)), Left) /= Empty);

               --  Color X's parent black and its grand parent red

               T.Color (Parent (T.Struct, X)) := Black;
               T.Color (Parent (T.Struct, Parent (T.Struct, X))) := Red;
               Right_Rotate (T.Struct, Parent (T.Struct, Parent (T.Struct, X)));

               --  We should now be done

               pragma Assert (Color (T, Parent (T.Struct, X)) = Black);

               pragma Assert
                 (for all I in Index_Type =>
                    (if Parent (T.Struct, I) = Empty
                        or else T.Color (Parent (T.Struct, I)) = Red
                     then T.Color (I) = Black));
            end if;
         else

            --  Y is X's uncle

            Y := Peek (T.Struct, Parent (T.Struct, Parent (T.Struct, X)), Left);
            if Color (T, Y) = Red then

               --  If Y is red, move both Y and X's parent to black and the
               --  grand parent to Red. This preserves the number of black node
               --  per branch.

               T.Color (Y) := Black;
               T.Color (Parent (T.Struct, X)) := Black;
               T.Color (Parent (T.Struct, Y)) := Red;

               --  The grand parent may now break the invariant

               X := Parent (T.Struct, Y);
            else

               --  Y is black. We will color the grand parent red and rotate it
               --  to the left. To do so, we need the left son of the parent
               --  to be black. If it is X, it is red, so we need to first
               --  rotate it to the right.

               if X = Peek (T.Struct, Parent (T.Struct, X), Left) then
                  X := Parent (T.Struct, X);
                  Right_Rotate (T.Struct, X);
               end if;

               pragma Assert (Parent (T.Struct, Parent (T.Struct, X)) /= Empty);
               pragma Assert (Peek (T.Struct,
                              Parent (T.Struct, Parent (T.Struct, X)), Right) /= Empty);

               --  Color X's parent black and its grand parent red

               T.Color (Parent (T.Struct, X)) := Black;
               T.Color (Parent (T.Struct, Parent (T.Struct, X))) := Red;
               Left_Rotate (T.Struct, Parent (T.Struct, Parent (T.Struct, X)));

               --  We should now be done

               pragma Assert (Color (T, Parent (T.Struct, X)) = Black);

               pragma Assert
                 (for all I in Index_Type =>
                    (if Parent (T.Struct, I) = Empty
                        or else T.Color (Parent (T.Struct, I)) = Red
                     then T.Color (I) = Black));
            end if;
         end if;
      end loop;

      pragma Assert
        (for all I in Index_Type =>
           (if I /= Root (T.Struct)
            and then (Parent (T.Struct, I) = Empty
              or else T.Color (Parent (T.Struct, I)) = Red)
            then T.Color (I) = Black));

      --  If we have colored the top red, we can safely color it back to black

      T.Color (Root (T.Struct)) := Black;
   end Insert;

end Red_Black_Trees;
