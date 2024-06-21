private package Illegal_Hide_Private.P_Child with
   SPARK_Mode
is

   type T is private;

private
   --  Hide annotation is illegal in a private child package
   pragma Annotate (GNATprove, Hide_Info, "Private_Part");

   type T is new Integer;

end Illegal_Hide_Private.P_Child;
