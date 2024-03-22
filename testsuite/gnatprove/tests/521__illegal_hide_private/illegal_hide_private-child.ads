package Illegal_Hide_Private.Child with
   SPARK_Mode
is

   function F return Boolean;

private
   --  The private part should be hidden for consistency with parent
   function F return Boolean is (F_Hidden);

end Illegal_Hide_Private.Child;
