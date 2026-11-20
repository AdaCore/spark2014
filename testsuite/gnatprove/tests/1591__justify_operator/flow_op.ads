package Flow_Op
  with SPARK_Mode
is
   procedure Stop
   with
     Import,
     Global       => null,
     No_Return,
     Always_Terminates,
     Program_Exit => True;

   --  Match the diagnostic as it appears on screen, including the operator
   --  name.

   function "&" (Left, Right : Integer) return Integer
   with Side_Effects, Program_Exit => True;
   pragma
     Annotate
       (GNATprove,
        Intentional,
        "function overriding operator ""&"" does not return on some paths",
        "");

   --  Match the same check using a suffix that excludes the operator name

   function "&" (Left, Right : Boolean) return Boolean
   with Side_Effects, Program_Exit => True;
   pragma
     Annotate
       (GNATprove,
        Intentional,
        "does not return on some paths",
        "");
end;
