private package Hidden_Private_Part.P_Child with
   SPARK_Mode
is
   --  Private child cannot have annotations.
   --  The private part of the parent is visible.

   function F return Boolean with Post => F'Result = True;

private

   function F return Boolean is (F_Hidden);

end Hidden_Private_Part.P_Child;
