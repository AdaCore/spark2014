package Hidden_Private_Part.Child_No_Priv with
   SPARK_Mode
is

   --  It is OK for a public child to not have a private part at all.

   function F return Boolean is (True);

end Hidden_Private_Part.Child_No_Priv;
