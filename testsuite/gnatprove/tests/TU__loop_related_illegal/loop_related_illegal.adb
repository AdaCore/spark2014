package body Loop_Related_Illegal
  with SPARK_Mode
is
   procedure Not_Within_Loop is
   --  TU: 6. A construct which is restricted to loops shall occur immediately
   --  within either:
   --  * the ``sequence_of_statements`` of a ``loop_statement``; or
   --  * the ``sequence_of_statements`` or ``declarative_part`` of a
   --    ``block_statement``.
   --  The construct is said to apply to the innermost enclosing loop.
   --  [Roughly speaking, a Loop_Invariant or Loop_Variant pragma shall only
   --  occur immediately within a loop statement except that intervening
   --  block statements are ignored for purposes of this rule.]
      X : Integer;
   begin
      X := 0;
      pragma Loop_Invariant (X = 10);
   end Not_Within_Loop;


   procedure Not_Immediately_Within_Loop is
   --  TU: 6. A construct which is restricted to loops shall occur immediately
   --  within either:
   --  * the ``sequence_of_statements`` of a ``loop_statement``; or
   --  * the ``sequence_of_statements`` or ``declarative_part`` of a
   --    ``block_statement``.
   --  The construct is said to apply to the innermost enclosing loop.
   --  [Roughly speaking, a Loop_Invariant or Loop_Variant pragma shall only
   --  occur immediately within a loop statement except that intervening
   --  block statements are ignored for purposes of this rule.]
      X : Integer := 100;
   begin
      loop
         if X > 0 then
            X := X - 1;
            pragma Loop_Invariant (X >= 0 and X < X'Loop_Entry);
         end if;
         exit when X = 0;
      end loop;
   end Not_Immediately_Within_Loop;


   procedure Not_A_Discrete_Type is
   --  TU: 7. The expression of a ``loop_variant_item`` shall be of any
   --  discrete type.
      type Real is digits 8;
      X : Real := 0.0;
   begin
      loop
         X := X + 0.00000001;
         pragma Loop_Variant (Increases => X);
         exit when X = 0.000001;
      end loop;
   end Not_A_Discrete_Type;


   procedure Illegal_Placement is
   --  TU: 5. A ``Loop_Entry`` ``attribute_reference`` shall occur within a
   --  ``Loop_Variant`` or ``Loop_Invariant`` pragma, or an ``Assert``,
   --  ``Assume`` or ``Assert_And_Cut`` pragma appearing in a position where a
   --  ``Loop_Invariant`` pragma would be allowed.
   --  [Roughly speaking, a ``Loop_Entry`` ``attribute_reference`` can occur in
   --  an ``Assert``, ``Assume`` or ``Assert_And_Cut`` pragma immediately
   --  within a loop statement except that intervening block statements are
   --  ignored for purposes of this rule.]
      X : Integer := 0;
   begin
      loop
         X := X + 1;
         exit when X = 10;
      end loop;
      pragma Assert (X'Loop_Entry = 0);
   end Illegal_Placement;


   procedure Illegal_Placement_2 is
   --  TU: 5. A ``Loop_Entry`` ``attribute_reference`` shall occur within a
   --  ``Loop_Variant`` or ``Loop_Invariant`` pragma, or an ``Assert``,
   --  ``Assume`` or ``Assert_And_Cut`` pragma appearing in a position where a
   --  ``Loop_Invariant`` pragma would be allowed.
   --  [Roughly speaking, a ``Loop_Entry`` ``attribute_reference`` can occur in
   --  an ``Assert``, ``Assume`` or ``Assert_And_Cut`` pragma immediately
   --  within a loop statement except that intervening block statements are
   --  ignored for purposes of this rule.]
      X : Integer := 0;
   begin
      loop
         X := X'Loop_Entry + 100;
         exit when X >= 10;
      end loop;
   end Illegal_Placement_2;


   procedure Cannot_Refer_To_Local_Variables is
   --  TU: 6. The prefix of a Loop_Entry ``attribute_reference`` shall not
   --  contain a use of an entity declared within the ``loop_statement`` but
   --  not within the prefix itself.
   --  [This rule is to allow the use of I in the following example:
   --  .. code-block:: ada
   --    loop
   --       pragma Assert
   --         ((Var > Some_Function (Param =>
   --            (for all I in T => F (I))))'Loop_Entry);
   --  In this example the value of the inequality ">" that would have been
   --  evaluated on entry to the loop is obtained even if the value of Var
   --  has since changed].
      X : Integer := 0;
   begin
      loop
         declare
            Local : Integer := 10;
         begin
            pragma Loop_Invariant (Local'Loop_Entry = 10);
         end;
         X := X + 1;
         exit when X = 10;
      end loop;
   end Cannot_Refer_To_Local_Variables;


   type Array_T is array (Integer range 1 .. 10) of Natural;

   procedure Does_Not_Apply_To_Innermost (Arr : in out Array_T;
                                          Idx : in out Positive) is
   begin
      Outer:
         loop
            if Idx in Arr'Range then
               Inner:
                  loop
                     Arr (Idx) := Arr (Idx) + 1;
                     pragma Loop_Invariant
                       (Arr (Idx) > Arr (Idx)'Loop_Entry (Outer));
                     Idx := Idx + 1;
                     if Idx = Arr'Last then
                        return;
                     end if;
                  end loop Inner;
            end if;
            Idx := Arr'First;
         end loop Outer;
   end Does_Not_Apply_To_Innermost;
end Loop_Related_Illegal;
