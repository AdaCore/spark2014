package body Types is

   Foo : Natural := 0;

   procedure Convert_To_U13 (Offset : Natural)
   is
      Fraction : constant Boolean := (13 + Offset) mod 8 = 0;
   begin
      --  Uncommenting the following assertion about Foo causes the next one to
      --  be proved by CVC4 in just 1 step. But without this assertion none of
      --  our provers can discharge the next one.
      --
      --  pragma Assert (2 ** Foo > 0);
      --
      --  Also removing the not really used declaration of Fraction causes the
      --  following assertion to be proved instantly.
      --
      --  Finally, changing the inequality from > to >= 0 below causes it to be
      --  proved, perhaps because the >= version almost exactly matches a lemma
      --  in why3/theories/int.why:
      --
      --    lemma Power_non_neg:
      --       forall x y. x >= 0 /\ y >= 0 -> power x y >= 0

      pragma Assert (2 ** Offset > 0);
   end Convert_To_U13;

end Types;
