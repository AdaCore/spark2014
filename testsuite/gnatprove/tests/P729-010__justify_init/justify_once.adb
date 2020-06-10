package body Justify_Once with SPARK_Mode is

   function Test (K : My_Kind) return My_Array is
      A : My_Array (1 .. 4);
   begin
      Check_Init (A);
      pragma Annotate (GNATprove, False_Positive, """A"" is not initialized",
                       "Fully_Init is fully initialized by default");
      case K is
         when One =>
            Update (A (1));
         when Two =>
            Update (A (2));
         when Three =>
            Update (A (3));
         when Four =>
            Update (A (4));
      end case;
      return A;
   end Test;

   function Test return Fully_Init is
      P : Fully_Init;
   begin
      Check_Init (P);
      pragma Annotate (GNATprove, False_Positive, """P"" is not initialized",
                       "Fully_Init is fully initialized by default");
      Update (P);
      return P;
   end Test;

end Justify_Once;
