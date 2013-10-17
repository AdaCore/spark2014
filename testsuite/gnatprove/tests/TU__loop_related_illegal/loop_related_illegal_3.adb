package body Loop_Related_Illegal_3
  with SPARK_Mode
is
   procedure Unevaluated (Par : out Integer) is
   --  TU: 7. The prefix of a Loop_Entry ``attribute_reference`` shall
   --  statically denote an entity, or shall denote an
   --  ``object_renaming_declaration``, if
   --  * the ``attribute_reference`` is potentially unevaluated; or
   --  * the ``attribute_reference`` does not apply to the innermost
   --    enclosing ``loop_statement``.
      X : Integer;
      Y : Integer := 100;
   begin
      loop
         X := 10;
         exit when Y <= X;
         pragma Loop_Invariant (Y > X'Loop_Entry);
         --  "X" might be uninitialized
         Y := Y - 1;
      end loop;
      Par := X + Y;
   end Unevaluated;
end Loop_Related_Illegal_3;
