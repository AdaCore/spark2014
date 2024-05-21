package Hidden_Private_Part.Child with
   SPARK_Mode
is

   --  Public child should have a consistent annotation with the parent.
   --  The private part of the parent is visible.

   function F return Boolean with Post => F'Result = True;

private
   pragma Annotate (GNATprove, Hide_Info, "Private_Part", Hidden_Private_Part.Child);

   function F return Boolean is (F_Hidden);

end Hidden_Private_Part.Child;
