package body Nested_Loops is
   -- termination proved
   procedure Proc with Annotate => (GNATprove, Terminating) is
      J : Integer := 2;
      X : Integer;
   begin
      while J < 5 loop
         J := J + 1;
         pragma Loop_Variant (Increases => J);
         for I in 1 .. 5 loop
            Pragma Loop_Variant (Increases => I);
            X := I;
            while X > 0 loop
               pragma Loop_Variant (Increases => X);
               null;
            end loop;
         end loop;
      end loop;
   end Proc;

   -- termination not proved
   procedure Proc2 with Annotate => (GNATprove, Terminating) is
      J : Integer := 2;
   begin
      while J < 5 loop
         J := J + 1;
         pragma Loop_Variant (Increases => J);
         for I in 1 .. 5 loop
            Pragma Loop_Variant (Increases => I);
            while True loop
               null;
            end loop;
         end loop;
      end loop;
   end Proc2;

   -- termination not proved
   procedure Proc3 with Annotate => (GNATprove, Terminating) is
      J : Integer := 2;
   begin
      while J < 5 loop
         J := J + 1;
         for I in 1 .. 5 loop
            while True loop
               null;
            end loop;
         end loop;
      end loop;
   end Proc3;

begin
   null;
end;
