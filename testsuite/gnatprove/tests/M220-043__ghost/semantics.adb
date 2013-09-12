package body Semantics is 

   ---------------------------
   -- Check_Assertion_Exprs --
   ---------------------------

   procedure Check_Assertion_Exprs (Formal : in out Integer) is
   begin
      pragma Assert (Formal + Ghost_Func > 0);
      pragma Assume (Formal + Ghost_Func > 0);

      for I in 1 .. 2 loop
         Formal := Formal + 1;

         pragma Loop_Invariant (Formal + Ghost_Func > 0);
         pragma Loop_Variant   (Increases => Formal + Ghost_Func);
      end loop;
   end Check_Assertion_Exprs;

   ---------------------------------
   -- Check_Within_Ghost_Function --
   ---------------------------------

   function Check_Within_Ghost_Function return Integer is
      procedure Nested_Non_Ghost (Var : Integer);
      --  Check a call to a ghost function from a nested non-ghost routine

      ----------------------
      -- Nested_Non_Ghost --
      ----------------------

      procedure Nested_Non_Ghost (Var : Integer) is
         Obj : constant Integer := Var + Ghost_Func + Ren_Ghost_Func;
      begin
         null;
      end Nested_Non_Ghost;

   --  Start of processing for Check_Within_Ghost_Function

   begin
      Nested_Non_Ghost (Ghost_Func);

      return Ren_Ghost_Func;
   end Check_Within_Ghost_Function;

   ----------------
   -- Ghost_Func --
   ----------------

   function Ghost_Func return Integer is
   begin
      return 0;
   end Ghost_Func;

end Semantics;
